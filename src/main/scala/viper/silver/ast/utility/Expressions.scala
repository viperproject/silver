// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

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
    case inh: Inhaling => isPure(inh.body)
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
      case fa@Forall(vs,ts,body) => Forall(vs,ts,asBooleanExp(body))(fa.pos,fa.info)
      case Unfolding(_, exp) => asBooleanExp(exp)
      case Applying(_, exp) => asBooleanExp(exp)
    })
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

  def subExps(e: Exp) = e.subnodes collect {
    case e: Exp => e
  }

  def containsPermissionIntrospection(e: Exp): Boolean = e.exists {
    case _: CurrentPerm => true
    case _: ForPerm => true
    case _ => false
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
          case f@FieldAccess(rcv, _) => List(NeCmp(rcv, NullLit()(p))(p), FieldAccessPredicate(f, WildcardPerm()(p))(p))
          case f: FuncApp => prog.findFunction(f.funcname).pres
          case Div(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
          case Mod(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
          case SeqIndex(s, idx) => List(GeCmp(idx, IntLit(0)(p))(p), LtCmp(idx, SeqLength(s)(p))(p))
          case MapLookup(m, k) => List(MapContains(k, m)(p))
          case Unfolding(pred, _) => List(pred)
          case Applying(wand, _) => List(wand)
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
