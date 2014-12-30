/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.ast._

/** Utility methods for expressions. */
object Expressions {
  def isPure(e: Exp): Boolean = e match {
    case _: AccessPredicate => false

    case UnExp(e0) => isPure(e0)
    case InhaleExhaleExp(in, ex) => isPure(in) && isPure(ex)
    case BinExp(e0, e1) => isPure(e0) && isPure(e1)
    case CondExp(cnd, thn, els) => isPure(cnd) && isPure(thn) && isPure(els)
    case Unfolding(_, in) => isPure(in) /* Assuming that the first argument is pure */
    case QuantifiedExp(_, e0) => isPure(e0)
    case Let(_, _, body) => isPure(body)

    case _: Literal
         | _: PermExp
         | _: FuncApp
         | _: DomainFuncApp
         | _: LocationAccess
         | _: AbstractLocalVar
         | _: SeqExp
         | _: SetExp
         | _: MultisetExp
    => true
  }

  def isHeapDependent(e: Exp, p: Program): Boolean = e existsDefined {
    case   _: AccessPredicate
         | _: LocationAccess =>

    case fapp: FuncApp if fapp.func(p).pres.exists(isHeapDependent(_, p)) =>
  }

  def purify(e: Exp): Exp = e.transform({
      case _: AccessPredicate => TrueLit()()
    })()

  def whenInhaling(e: Exp) = e.transform()(post = {
    case InhaleExhaleExp(in, _) => in
  })

  def whenExhaling(e: Exp) = e.transform()(post = {
    case InhaleExhaleExp(_, ex) => ex
  })

  /** In an expression, instantiate a list of variables with given expressions. */
  def instantiateVariables[E <: Exp]
                          (exp: E, variables: Seq[AbstractLocalVar], values: Seq[Exp])
                          : E = {

    val argNames = (variables map (_.name)).zipWithIndex

    def actualArg(formalArg: String): Option[Exp] = {
      argNames.find(x => x._1 == formalArg) map {
        case (_, idx) => values(idx)
      }
    }

    val res = exp.transform {
      case AbstractLocalVar(name) if actualArg(name).isDefined => actualArg(name).get
    }()
    res
  }

  /* See http://stackoverflow.com/a/4982668 for why the implicit is here. */
  def instantiateVariables[E <: Exp]
                          (exp: E, variables: Seq[LocalVarDecl], values: Seq[Exp])
                          (implicit di: DummyImplicit)
                          : E =

    instantiateVariables(exp, variables map (_.localVar), values)

  def subExps(e: Exp) = e.subnodes collect {
    case e: Exp => e
  }

  // note: dependency on program for looking up function preconditions
  def proofObligations(e: Exp): (Program => Seq[Exp]) = ((prog:Program) => {
    e.reduceTree[Seq[Exp]] {
      (n: Node, subConds: Seq[Seq[Exp]]) =>
        val p = n match {
          case n: Positioned => n.pos
          case _ => NoPosition
        }
        // Conditions for the current node.
        val conds = n match {
          case f@FieldAccess(rcv, _) => List(NeCmp(rcv, NullLit()(p))(p), FieldAccessPredicate(f, WildcardPerm()(p))(p))
          case f: FuncApp => prog.findFunction(f.funcname).pres
          case Div(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
          case Mod(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
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
          case And(left, _) => {
            val Seq(leftConds, rightConds) = nonTrivialSubConds
            reduceAndProofObs(left, leftConds, rightConds, p)
          }
          case Implies(left, _) => {
            val Seq(leftConds, rightConds) = nonTrivialSubConds
            reduceImpliesProofObs(left, leftConds, rightConds, p)
          }
          case Or(left, _) => {
            val Seq(leftConds, rightConds) = nonTrivialSubConds
            reduceOrProofObs(left, leftConds, rightConds, p)
          }
          case CondExp(cond, _, _) => {
            val Seq(condConds, thenConds, elseConds) = nonTrivialSubConds
            reduceCondExpProofObs(cond, condConds, thenConds, elseConds, p)
          }
          case _ => subConds.flatten
        }
        // The condition of the current node has to be at the end because the subtrees have to be well-formed first.
        finalSubConds ++ conds
    }
  })

  /** Calculates the proof obligations for a conditional expression given the proof obligations of the subexpressions. */
  def reduceCondExpProofObs(cond: Exp, condConds: Seq[Exp], thenConds: Seq[Exp], elseConds: Seq[Exp], p: Position): Seq[Exp] = {
    val guardedBodyConds = if (!thenConds.isEmpty || !elseConds.isEmpty) {
      val combinedThenCond = if (!thenConds.isEmpty)
        thenConds reduce {
          (a, b) => And(a, b)(p)
        }
      else TrueLit()(p)
      val combinedElseCond = if (!elseConds.isEmpty)
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
    val guard = purify(left)
    reduceLazyBinOpProofObs(guard, leftConds, rightConds, p)
  }

  /** Calculates the proof obligations of an implication given the proof obligations of the subexpressions. */
  def reduceOrProofObs(left: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position) =
    reduceLazyBinOpProofObs(Not(left)(p), leftConds, rightConds, p)

  /** Calculates the proof obligations of a binary expression which has a second half which will only be evaluated
    * if `evalCond` is true given the proof obligations of the subexpressions. */
  def reduceLazyBinOpProofObs(evalCond: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position): Seq[Exp] = {
    val guardedRightConds = if (!rightConds.isEmpty) {
      val combinedRightCond = rightConds reduce {
        (a, b) => And(a, b)(p)
      }
      List(Implies(evalCond, combinedRightCond)(p))
    } else Nil
    leftConds ++ guardedRightConds
  }

  /**
   * Generates trigger sets to cover the variables "vs", by searching the
   * expression "toSearch". Returns a list of pairs of lists of trigger sets
   * couple with the extra variables they require to be quantified over
   * (each list of triggers must contain trigger sets which employ exactly
   * the same extra variables).
   */
  def generateTrigger(exp: QuantifiedExp): Seq[(Seq[Trigger], Seq[LocalVarDecl])] = {
    TriggerGeneration.generateTriggers(exp.variables map (_.localVar), exp.exp)
                     .map{case (triggers, vars) => (triggers, vars map (v => LocalVarDecl(v.name, v.typ)()))}
  }

  object TriggerGeneration extends GenericTriggerGenerator[Node, Type, Exp, LocalVar, QuantifiedExp, PossibleTrigger,
                                                           ForbiddenInTrigger, Old, WrappingTrigger, Trigger] {

    protected def hasSubnode(root: Node, child: Node) = root.hasSubnode(child)
    protected def visit[A](root: Node)(f: PartialFunction[Node, A]) = root.visit(f)
    protected def deepCollect[A](root: Node)(f: PartialFunction[Node, A]) = root.deepCollect(f)
    protected def reduceTree[A](root: Node)(f: (Node, Seq[A]) => A) = root.reduceTree(f)
    protected def transform[N <: Node](root: N)(f: PartialFunction[Node, Node]) = root.transform(f)()
    protected def quantifiedVariables(q: QuantifiedExp) = q.variables map (_.localVar)
    protected def exps(t: Trigger) = t.exps

    protected def Trigger(exps: Seq[Exp]) = viper.silver.ast.Trigger(exps)()
    protected def Var(id: String, typ: Type) = LocalVar(id)(typ)

    protected val wrapperMap: Map[Class[_], PossibleTrigger => WrappingTrigger] = Map(
      classOf[Old] -> (pt => OldTrigger(pt)(pt.pos,pt.info)))
  }
}
