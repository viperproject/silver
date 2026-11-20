// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import scala.collection.mutable
import scala.reflect.ClassTag
import viper.silver.ast._
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.utility.Triggers.{DefaultTriggerGeneration, TriggerGeneration}
import viper.silver.utility.Sanitizer

/** Utility methods for expressions. */
object Expressions {
  def isPure(e: Exp): Boolean = e match {
    case   _: AccessPredicate
         | _: MagicWand
         => false

    case UnExp(e0) => isPure(e0)
    case InhaleExhaleExp(in, ex) => isPure(in) && isPure(ex)
    case BinExp(e0, e1) => isPure(e0) && isPure(e1)
    case CondExp(cnd, thn, els) => isPure(cnd) && isPure(thn) && isPure(els)
    case unf: Unfolding => isPure(unf.body)
    case app: Applying => isPure(app.body)
    case Asserting(a, e) => isPure(e)
    case QuantifiedExp(_, e0) => isPure(e0)
    case Let(_, _, body) => isPure(body)
    case e: ExtensionExp => e.extensionIsPure

    case   _: Literal
         | _: PermExp
         | _: FuncApp
         | _: DomainFuncApp
         | _: BackendFuncApp
         | _: LocationAccess
         | _: AbstractLocalVar
         | _: SeqExp
         | _: SetExp
         | _: MultisetExp
         | _: MapExp
         | _: ForPerm
      => true
  }

  def isTopLevelHeapDependent(e: Exp, p:Program) : Boolean = e match {
    case   _: AccessPredicate
           | _: LocationAccess
           | _: MagicWand => true

    case fapp: FuncApp if couldBeHeapDependent(fapp.func(p),p) => true
    case _ => false
  }

  def isHeapDependent(e: Exp, p: Program): Boolean = e existsDefined {
    case ee:Exp if isTopLevelHeapDependent(ee,p) =>
      // note: type of existsDefined doesn't guarantee we will only see Exp-typed nodes, but these are the transitive subnodes of e
  }

  def dependsOnCurrentHeap(e:Exp, p:Program, treatMagicWandStatesAsCurrentStates:Boolean = false) : Boolean = {
    var depends = false;

    def go(root: Exp, p:Program, inCurrentState:Boolean): Unit = {
      root.visitWithContextManually[Boolean,Unit](inCurrentState)(
        currentState => //if (depends) PartialFunction.empty // we're done
          //else
        {
          case LabelledOld(ee, LabelledOld.LhsOldLabel) =>
            if (treatMagicWandStatesAsCurrentStates)
              go(ee,p,true)
            else
              () // do nothing; if we're under some kind of old expression, nothing can depend on the current state
          case o:OldExp => // any other old expression never counts as the current state
            if (treatMagicWandStatesAsCurrentStates) // we should recurse just in case we hit a nested old[lhs](..)
              go(o.exp,p,false)
            else
              () // do nothing; if we're under some kind of old expression, nothing can depend on the current state
          case ee:Exp => {
            if (currentState && Expressions.isTopLevelHeapDependent(root,p)) // this also catches resources
              depends = true // we're done
            else
              ee.subExps.foreach(sub => {
                if(depends) () else go(sub,p,currentState)
              })
          }
        }
      )
    }
    go(e,p,true)
    depends
  }

  def couldBeHeapDependent(f: Function, p:Program) : Boolean = f.pres.exists(isHeapDependent(_, p))

  def asBooleanExp(e: Exp): Exp = {
    e.transform({
      case _: AccessPredicate | _: MagicWand => TrueLit()()
      case fa@Forall(vs,ts,body) => Forall(vs, ts, asBooleanExp(body))(fa.pos, fa.info, fa.errT)
      case Unfolding(_, exp) => asBooleanExp(exp)
      case Applying(_, exp) => asBooleanExp(exp)
      case ass@Asserting(a, exp) => Asserting(asBooleanExp(a), asBooleanExp(exp))(ass.pos, ass.info, ass.errT)
    })
  }

  /** Returns only the functional parts of an expression.
    * Note: Result is likely not self-framing.
    */
  def asPureFragment(e: Exp): Option[Exp] = {
    asFragment(e, pureFragment = true)
  }

  /** Returns only the access/permission parts of an expression.
    * Note: Result may not be well-defined on its own if functional properties are dropped,
    * e.g. index bounds in QPs.
    */
  def asAccessFragment(e: Exp): Option[Exp] = {
    asFragment(e, pureFragment = false)
  }

  private def asFragment(e: Exp, pureFragment: Boolean): Option[Exp] = {
    def rec(e2: Exp): Option[Exp] = asFragment(e2, pureFragment)

    e match {
      case _: AccessPredicate => if (pureFragment) None else Some(e)
      case ie@InhaleExhaleExp(in, ex) => for {
        in2 <- rec(in)
        ex2 <- rec(ex)
      } yield InhaleExhaleExp(in2, ex2)(ie.pos, ie.info, ie.errT)
      case imp@Implies(left, right) => rec(right).map(Implies(left, _)(imp.pos, imp.info, imp.errT))
      case and@And(left, right) =>
        (rec(left), rec(right)) match {
          case (Some(left2), Some(right2)) => Some(And(left2, right2)(and.pos, and.info, and.errT))
          case (Some(left2), None) => Some(left2)
          case (None, Some(right2)) => Some(right2)
          case (None, None) => None
        }
      case ite@CondExp(cond, thn, els) =>
        (rec(thn), rec(els)) match {
          case (Some(thn2), Some(els2)) => Some(CondExp(cond, thn2, els2)(ite.pos, ite.info, ite.errT))
          case (Some(thn2), None) => Some(Implies(cond, thn2)(ite.pos, ite.info, ite.errT))
          case (None, Some(els2)) =>
            Some(Implies(Not(cond)(cond.pos, cond.info, cond.errT), els2)(ite.pos, ite.info, ite.errT))
          case (None, None) => None
        }
      case unf@Unfolding(acc, body) => rec(body).map(Unfolding(acc, _)(unf.pos, unf.info, unf.errT))
      case app@Applying(wand, body) => rec(body).map(Applying(wand, _)(app.pos, app.info, app.errT))
      case ass@Asserting(a, body) => rec(body).map(Asserting(a, _)(ass.pos, ass.info, ass.errT))
      case let@Let(variable, exp, body) => rec(body).map(Let(variable, exp, _)(let.pos, let.info, let.errT))
      case qa@Forall(_, _, exp) => rec(exp).map(exp2 => qa.copy(exp = exp2)(qa.pos, qa.info, qa.errT))
      case qe@Exists(_, _, exp) => rec(exp).map(exp2 => qe.copy(exp = exp2)(qe.pos, qe.info, qe.errT))
      case ext: ExtensionExp => if (ext.extensionIsPure == pureFragment) Some(ext) else None
      case _: Literal
           | _: AbstractLocalVar
           | _: BinExp
           | _: UnExp
           | _: LocationAccess
           | _: PermExp
           | _: ForPerm
           | _: FuncLikeApp
           | _: SeqExp
           | _: SetExp
           | _: MultisetExp
           | _: MapExp
      => if (pureFragment) Some(e) else None
    }
  }

  def whenInhaling(e: Exp) = e.transform({
    case InhaleExhaleExp(in, _) => in
  }, Traverse.BottomUp)

  def whenExhaling(e: Exp) = e.transform({
    case InhaleExhaleExp(_, ex) => ex
  }, Traverse.BottomUp)

  def contains[T <: Node : ClassTag](expressions: Seq[Exp]) = {
    expressions.exists(_.contains[T])
  }

  // collects the free variables in an expression
  def freeVariables(e: Exp): Set[AbstractLocalVar] = freeVariablesExcluding(e, Set[AbstractLocalVar]())

  // collects the free variables in an expression, *excluding* a given sequence of variables to ignore
  def freeVariablesExcluding(e: Exp, toIgnore: Seq[AbstractLocalVar]): Set[AbstractLocalVar] =
    freeVariablesExcluding(e, toIgnore.toSet)

  // collects the free variables in an expression, *excluding* a given set of variables to ignore
  def freeVariablesExcluding(e: Exp, toIgnore: Set[AbstractLocalVar]): Set[AbstractLocalVar] = {
    e.shallowCollect{
      case Let(binding, exp, body) =>
        freeVariablesExcluding(exp, toIgnore) union freeVariablesExcluding(body, toIgnore + binding.localVar)
      case q: QuantifiedExp =>
        val ignoring = toIgnore union (q.variables map (_.localVar)).toSet
        q.subExps.flatMap(freeVariablesExcluding(_, ignoring))
      case v@AbstractLocalVar(_) if !toIgnore.contains(v) =>
        Seq(v)
    }.flatten.toSet
  }

  /** Collects all variables that are actually contained in the given node, filtering out let-variables
    * as well as variables used in expressions bound to let-variables which are not used in the let body.  */
  def getContainedVariablesExcludingLet(e: Node): Set[LocalVar] = {
    Visitor.deepCollect[Node, Set[LocalVar]](Seq(e), {
      case _: Let => Seq()
      case n => Nodes.subnodes(n)
    }) {
      case lv: LocalVar => Set(lv)
      case Let(v, e, body) =>
        val bodyVars = getContainedVariablesExcludingLet(body)
        if (bodyVars.contains(v.localVar))
          bodyVars - v.localVar ++ getContainedVariablesExcludingLet(e)
        else
          bodyVars - v.localVar
    }.flatten.toSet
  }

  /** In an expression, rename a list (domain) of variables with given (range) variables. */
  def renameVariables[E <: Exp]
                     (exp: E, domain: Seq[AbstractLocalVar], range: Seq[AbstractLocalVar])
                     : E = {

    val argNames = (domain map (_.name)).zipWithIndex

    def actualArg(formalArg: String): Option[AbstractLocalVar] = {
      argNames.find(x => x._1 == formalArg) map {
        case (_, idx) => range(idx)
      }
    }

    val res = exp.transform {
      case AbstractLocalVar(name) if actualArg(name).isDefined => actualArg(name).get
      case orig@LocalVarDecl(name,typ) if actualArg(name).isDefined => LocalVarDecl(actualArg(name).get.name,typ)(orig.pos,orig.info)
    }
    res
  }

  /** In an expression, instantiate a list of variables with given expressions. */
  def instantiateVariables[E <: Exp]
                          (exp: E, variables: Seq[AbstractLocalVar], values: Seq[Exp])
                          : E = {
    assert(variables.size == values.size, "The amount of values must match the amount of variables they are replacing")

    Sanitizer.replaceFreeVariablesInExpression(exp, variables.map(_.name).zip(values).toMap, Set())
  }

  /* See http://stackoverflow.com/a/4982668 for why the implicit is here. */
  def instantiateVariables[E <: Exp](exp: E, variables: Seq[LocalVarDecl], values: Seq[Exp], scope: Set[String])
                                    (implicit di: DummyImplicit): E = {
    assert(variables.size == values.size, "The amount of values must match the amount of variables they are replacing")

    Sanitizer.replaceFreeVariablesInExpression(exp, variables.map(_.localVar.name).zip(values).toMap, scope)
  }

  /** Returns true iff `e1` and `e2` are equal after replacing each let-bound variable by its value, without
    * constructing the expressions with inlined lets. Quantified variables are compared by their binding, i.e.
    * up to renaming. A let-bound variable that is used in an `old` expression but bound outside of it is only
    * equal to a let-bound variable that is bound in the same state to an equal value, since its value is not
    * evaluated in the old state. Other expressions that change the state, such as `applying`, are not taken
    * into account.
    *
    * Each pair of subexpressions of `e1` and `e2` is compared at most once per pair of the environments of
    * let-bound variables they are compared in. Hence, the comparison takes time polynomial in the sizes of `e1`
    * and `e2`, even if inlining their lets makes them exponentially larger, as, e.g., for
    * `let x1 == (f(x0, x0)) in let x2 == (f(x1, x1)) in ...`.
    */
  def equalModuloLets(e1: Exp, e2: Exp): Boolean =
    new ModuloLets().equal(e1, Map.empty, e2, Map.empty, None)

  /** Returns the expression at the top of `e` after resolving the lets around it and a let-bound variable at its
    * top, e.g. `f(x)` for `let x == (q(i)) in f(x)` and `q(i)` for `let x == (q(i)) in x`. The subexpressions of the
    * result may contain variables bound by the lets of `e`.
    */
  def topLevelModuloLets(e: Exp): Exp = new ModuloLets().top(e, Map.empty)

  /** See [[equalModuloLets]] and [[topLevelModuloLets]]. Environments map the names of bound variables to their bindings: a let-bound
    * variable to a [[LetBinding]] and a quantified variable to an object that represents its binding. A state is
    * `None` for the current state, `Some(None)` for the state of `old` and `Some(Some(label))` for the state of
    * `old[label]`.
    */
  private class ModuloLets {
    private type Env = Map[String, AnyRef]
    private type State = Option[Option[String]]

    /** A variable bound to `exp`, which is evaluated with `env` in `state`. */
    private class LetBinding(val exp: Exp, val env: Env, val state: State)

    /** The arguments of a call of `equal`, compared by reference, except for the state. */
    private class Comparison(val e1: Exp, val env1: Env, val e2: Exp, val env2: Env, val state: State) {
      override def equals(other: Any): Boolean = other match {
        case c: Comparison => (e1 eq c.e1) && (env1 eq c.env1) && (e2 eq c.e2) && (env2 eq c.env2) && state == c.state
        case _ => false
      }
      override def hashCode(): Int = (System.identityHashCode(e1), System.identityHashCode(env1),
        System.identityHashCode(e2), System.identityHashCode(env2), state).hashCode()
    }

    private val results = mutable.HashMap.empty[Comparison, Boolean]

    def top(e: Exp, env: Env): Exp = e match {
      case Let(v, e0, body) => top(body, env + (v.name -> new LetBinding(e0, env, None)))
      case v: LocalVar => env.get(v.name) match {
        case Some(b: LetBinding) => top(b.exp, b.env)
        case _ => v
      }
      case _ => e
    }

    def equal(e1: Exp, env1: Env, e2: Exp, env2: Env, state: State): Boolean = {
      val comparison = new Comparison(e1, env1, e2, env2, state)
      results.get(comparison) match {
        case Some(result) => result
        case None =>
          val result = compare(e1, env1, e2, env2, state)
          results.put(comparison, result)
          result
      }
    }

    private def compare(e1: Exp, env1: Env, e2: Exp, env2: Env, state: State): Boolean = (e1, e2) match {
      case _ if (e1 eq e2) && (env1 eq env2) => true
      case (Let(v, e0, body), _) => equal(body, env1 + (v.name -> new LetBinding(e0, env1, state)), e2, env2, state)
      case (_, Let(v, e0, body)) => equal(e1, env1, body, env2 + (v.name -> new LetBinding(e0, env2, state)), state)
      case (v1: LocalVar, v2: LocalVar) if env1.contains(v1.name) && env2.contains(v2.name) =>
        (env1(v1.name), env2(v2.name)) match {
          case (b1: LetBinding, b2: LetBinding) => b1.state == b2.state && equal(b1.exp, b1.env, b2.exp, b2.env, b1.state)
          case (b1: LetBinding, _) => b1.state == state && equal(b1.exp, b1.env, e2, env2, state)
          case (_, b2: LetBinding) => b2.state == state && equal(e1, env1, b2.exp, b2.env, state)
          case (binding1, binding2) => binding1 eq binding2
        }
      case (v1: LocalVar, _) if env1.contains(v1.name) => env1(v1.name) match {
        case b1: LetBinding if b1.state == state => equal(b1.exp, b1.env, e2, env2, state)
        case _ => false
      }
      case (_, v2: LocalVar) if env2.contains(v2.name) => env2(v2.name) match {
        case b2: LetBinding if b2.state == state => equal(e1, env1, b2.exp, b2.env, state)
        case _ => false
      }
      case (q1: QuantifiedExp, q2: QuantifiedExp)
          if q1.getClass == q2.getClass && q1.variables.map(_.typ) == q2.variables.map(_.typ) =>
        val bindings = q1.variables.map(_ => new AnyRef)
        // The first element of a quantifier is the sequence of its variables
        equalElements(q1, env1 ++ q1.variables.map(_.name).zip(bindings),
                      q2, env2 ++ q2.variables.map(_.name).zip(bindings), state, from = 1)
      case (Old(o1), Old(o2)) => equal(o1, env1, o2, env2, Some(None))
      case (LabelledOld(o1, l1), LabelledOld(o2, l2)) => l1 == l2 && equal(o1, env1, o2, env2, Some(Some(l1)))
      case (DebugLabelledOld(o1, l1), DebugLabelledOld(o2, l2)) => l1 == l2 && equal(o1, env1, o2, env2, Some(Some(l1)))
      case _ => e1.getClass == e2.getClass && equalElements(e1, env1, e2, env2, state)
    }

    /** Compares the elements of `p1` and `p2`, starting with the element at index `from`. */
    private def equalElements(p1: Product, env1: Env, p2: Product, env2: Env, state: State, from: Int = 0): Boolean =
      p1.productArity == p2.productArity &&
        (from until p1.productArity).forall(k => equalElement(p1.productElement(k), env1, p2.productElement(k), env2, state))

    private def equalElement(a: Any, env1: Env, b: Any, env2: Env, state: State): Boolean = (a, b) match {
      case (a: Exp, b: Exp) => equal(a, env1, b, env2, state)
      case (as: Seq[_], bs: Seq[_]) => as.size == bs.size && as.lazyZip(bs).forall(equalElement(_, env1, _, env2, state))
      case (Some(a), Some(b)) => equalElement(a, env1, b, env2, state)
      case (a: Node with Product, b: Node with Product) => a.getClass == b.getClass && equalElements(a, env1, b, env2, state)
      case (a, b) => a == b
    }
  }

  def subExps(e: Exp) = e.subnodes collect {
    case e: Exp => e
  }

  def containsPermissionIntrospection(e: Exp): Boolean = e.exists {
    case _: CurrentPerm => true
    case _: ForPerm => true
    case _ => false
  }

  def isKnownWellDefined(e: Exp, program: Option[Program]): Boolean = {
    e match {
      case FieldAccessPredicate(FieldAccess(rcv, _), prm) =>
        // Extra case for field access predicates because the contained field access does NOT require already having the field permission.
        isKnownWellDefined(rcv, program) && (prm.isEmpty || isKnownWellDefined(prm.get, program))
      case _: FieldAccess | _: Unfolding | _: Applying | _: Asserting => false
      case _: SeqIndex | _: MapLookup => false
      case _: Div | _: Mod => false
      case f: FuncApp =>
        program match {
          case Some(p) => p.findFunction(f.funcname).pres.isEmpty && f.args.forall(isKnownWellDefined(_, program))
          case None => false // conservative
        }
      case other => other.subExps.forall(isKnownWellDefined(_, program))
    }
  }

  // note: dependency on program for looking up function preconditions
  def proofObligations(e: Exp): (Program => Seq[Exp]) = (prog: Program) => {
    e.reduceTree[Seq[Exp]] {
      (n: Node, subConds: Seq[Seq[Exp]]) =>
        val p = n match {
          case n: Positioned => n.pos
          case _ => NoPosition
        }
        // Conditions for the current node.
        val conds: Seq[Exp] = n match {
          case f@FieldAccess(rcv, _) => List(NeCmp(rcv, NullLit()(p))(p), FieldAccessPredicate(f, Some(WildcardPerm()(p)))(p))
          case f: FuncApp => prog.findFunction(f.funcname).pres
          case Div(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
          case Mod(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
          case SeqIndex(s, idx) => List(GeCmp(idx, IntLit(0)(p))(p), LtCmp(idx, SeqLength(s)(p))(p))
          case MapLookup(m, k) => List(MapContains(k, m)(p))
          case Unfolding(pred, _) => List(pred)
          case Applying(wand, _) => List(wand)
          case Asserting(a, _) => List(a)
          case _ => Nil
        }
        // Only use non-trivial conditions for the subnodes.
        val nonTrivialSubConds = subConds.map {
          m => m.filter {
            _ != TrueLit()()
          }
        }
        // Combine the conditions of the subnodes depending on what node we currently have.
        val finalSubConds = n match {
          case And(left, _) =>
            val Seq(leftConds, rightConds, Seq()) = nonTrivialSubConds
            reduceAndProofObs(left, leftConds, rightConds, p)
          case Implies(left, _) =>
            val Seq(leftConds, rightConds, Seq()) = nonTrivialSubConds
            reduceImpliesProofObs(left, leftConds, rightConds, p)
          case Or(left, _) =>
            val Seq(leftConds, rightConds, Seq()) = nonTrivialSubConds
            reduceOrProofObs(left, leftConds, rightConds, p)
          case CondExp(cond, _, _) =>
            val Seq(condConds, thenConds, elseConds, Seq()) = nonTrivialSubConds
            reduceCondExpProofObs(cond, condConds, thenConds, elseConds, p)
          case _ => subConds.flatten
        }
        // The condition of the current node has to be at the end because the subtrees have to be well-formed first.
        finalSubConds ++ conds
    }
  }

  /** Calculates the proof obligations for a conditional expression given the proof obligations of the subexpressions. */
  def reduceCondExpProofObs(cond: Exp, condConds: Seq[Exp], thenConds: Seq[Exp], elseConds: Seq[Exp], p: Position): Seq[Exp] = {
    val guardedBodyConds = if (thenConds.nonEmpty || elseConds.nonEmpty) {
      val combinedThenCond = if (thenConds.nonEmpty)
        thenConds reduce {
          (a, b) => And(a, b)(p)
        }
      else TrueLit()(p)
      val combinedElseCond = if (elseConds.nonEmpty)
        elseConds reduce {
          (a, b) => And(a, b)(p)
        }
      else TrueLit()(p)
      List(CondExp(cond, combinedThenCond, combinedElseCond)(p))
    } else Nil
    condConds ++ guardedBodyConds
  }

  /** Calculates the proof obligations of an implication given the proof obligations of the subexpressions. */
  def reduceImpliesProofObs(left: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position) =
    reduceLazyBinOpProofObs(left, leftConds, rightConds, p)

  /** Calculates the proof obligations of an implication given the proof obligations of the subexpressions. */
  def reduceAndProofObs(left: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position) = {
    // We want to make the proof obligations as weak as possible, but we cannot use access predicates as guards,
    // so we need to remove them and make the guard weaker. This makes the proof obligations slightly too strong,
    // but it is the best we can do.
    val guard = asBooleanExp(left)
    reduceLazyBinOpProofObs(guard, leftConds, rightConds, p)
  }

  /** Calculates the proof obligations of an implication given the proof obligations of the subexpressions. */
  def reduceOrProofObs(left: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position) =
    reduceLazyBinOpProofObs(Not(left)(p), leftConds, rightConds, p)

  /** Calculates the proof obligations of a binary expression which has a second half which will only be evaluated
    * if `evalCond` is true given the proof obligations of the subexpressions. */
  def reduceLazyBinOpProofObs(evalCond: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position): Seq[Exp] = {
    val guardedRightConds = if (rightConds.nonEmpty) {
      val combinedRightCond = rightConds reduce {
        (a, b) => And(a, b)(p)
      }
      List(Implies(evalCond, combinedRightCond)(p))
    } else Nil
    leftConds ++ guardedRightConds
  }

  def isForbiddenInTrigger(n: Node): Boolean = n match {
    case _: ForbiddenInTrigger => true
    case ee: ExtensionExp => ee.extensionIsForbiddenInTrigger()
    case _ => false
  }

  /** See [[viper.silver.ast.utility.Triggers.TriggerGeneration.generateTriggerSetGroups]] */
  def generateTriggerGroups(exp: QuantifiedExp, tg: TriggerGeneration = DefaultTriggerGeneration): Seq[(Seq[tg.TriggerSet], Seq[LocalVarDecl])] = {
    tg.generateTriggerSetGroups(exp.variables map (_.localVar), exp.exp)
      .map{case (triggers, vars) => (triggers, vars map (v => LocalVarDecl(v.name, v.typ)()))}
  }

  /** Returns the first group of trigger sets (together with newly introduced
    * variables) returned by [[Expressions.generateTriggerGroups]], or `None`
    * if the latter didn't return any group.
    */
  def generateTriggerSet(exp: QuantifiedExp, tg: TriggerGeneration = DefaultTriggerGeneration): Option[(Seq[LocalVarDecl], Seq[tg.TriggerSet])] = {
    val gen = Expressions.generateTriggerGroups(exp, tg)

    if (gen.nonEmpty)
      gen.find(pair => pair._2.isEmpty) match {
        case Some((newTriggers, _)) =>
          Some((exp.variables, newTriggers))

        case None =>
            if (exp.isPure) {
              val (triggers, extraVariables) = gen.head // somewhat arbitrarily take the first choice
              Some((exp.variables ++ extraVariables, triggers))
            } else {
              gen.find(candidate => candidate._2.isEmpty) match {
                case None => None
                case Some((triggers,_)) => Some(exp.variables, triggers)
              } // extra variables cannot be added to quantified permissions, since we don't support nested quantification, yet
            }

      }
    else
      None
  }

  /** Returns the top-level conjuncts of the given expression. */
  def topLevelConjuncts(e: Exp): Seq[Exp] = e match {
    case And(e1, e2) => topLevelConjuncts(e1) ++ topLevelConjuncts(e2)
    case _ => Seq(e)
  }
}
