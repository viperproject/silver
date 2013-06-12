package semper.sil.ast.utility

import semper.sil.ast._

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

    case  _: Literal
        | _: PermExp
        | _: FuncApp
        | _: DomainFuncApp
        | _: LocationAccess
        | _: AbstractLocalVar
        | _: SeqExp
    => true
  }

  def whenInhaling(e: Exp) = e.transform()(post = {
    case InhaleExhaleExp(in, _) => in
  })

  def whenExhaling(e: Exp) = e.transform()(post = {
    case InhaleExhaleExp(_, ex) => ex
  })

  /**
   * In an expression, instantiate a list of variables with given expressions.
   */
  def instantiateVariables(exp: Exp, variables: Seq[LocalVarDecl], values: Seq[Exp]): Exp = {
    val argNames = (variables map (_.name)).zipWithIndex
    def actualArg(formalArg: String): Option[Exp] = {
      argNames.find(x => x._1 == formalArg) map {
        case (_, idx) => values(idx)
      }
    }
    exp.transform {
      case LocalVar(name) if actualArg(name).isDefined => actualArg(name).get
    }()
  }

  def subExps(e: Exp) = e.subnodes collect { case e: Exp => e }

  def proofObligations(e: Exp): Seq[Exp] = {
    e.reduceTree[Seq[Exp]] { (n: Node, subConds: Seq[Seq[Exp]]) =>
      val p = n match {
        case n: Positioned => n.pos
        case _ => NoPosition
      }
      // Conditions for the current node.
      val conds = n match {
        case f@FieldAccess(rcv, _) => List(NeCmp(rcv, NullLit()(p))(p), FieldAccessPredicate(f, WildcardPerm()(p))(p))
        case f: FuncApp => f.pres
        case Div(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
        case Mod(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
        case _ => Nil
      }
      // Only use non-trivial conditions for the subnodes.
      val nonTrivialSubConds = subConds.map { m => m.filter { _ != TrueLit()() } }
      // Combine the conditions of the subnodes depending on what node we currently have.
      val finalSubConds = n match {
        case And(left, _) => {
          val Seq(leftConds, rightConds) = nonTrivialSubConds
          val guardedRightConds = if (!rightConds.isEmpty) {
            val combinedRightCond = rightConds reduce { (a, b) => And(a, b)(p) }
            List(Implies(left, combinedRightCond)(p))
          } else Nil
          leftConds ++ guardedRightConds
        }
        case Implies(left, _) => {
          val Seq(leftConds, rightConds) = nonTrivialSubConds
          val guardedRightConds = if (!rightConds.isEmpty) {
            val combinedRightCond = rightConds reduce { (a, b) => And(a, b)(p) }
            List(Implies(left, combinedRightCond)(p))
          } else Nil
          leftConds ++ guardedRightConds
        }
        case Or(left, _) => {
          val Seq(leftConds, rightConds) = nonTrivialSubConds
          val guardedRightConds = if (!rightConds.isEmpty) {
            val combinedRightCond = rightConds reduce { (a, b) => And(a, b)(p) }
            List(Implies(Not(left)(p), combinedRightCond)(p))
          } else Nil
          leftConds ++ guardedRightConds
        }
        case CondExp(cond, _, _) => {
          val Seq(condConds, thenConds, elseConds) = nonTrivialSubConds
          val guardedBodyConds = if (!thenConds.isEmpty || !elseConds.isEmpty) {
            val combinedThenCond = if (!thenConds.isEmpty)
              thenConds reduce { (a, b) => And(a, b)(p) }
            else TrueLit()(p)
            val combinedElseCond = if (!elseConds.isEmpty)
              elseConds reduce { (a, b) => And(a, b)(p) }
            else TrueLit()(p)
            List(CondExp(cond, combinedThenCond, combinedElseCond)(p))
          } else Nil
          condConds ++ guardedBodyConds
        }
        case _ => subConds.flatten
      }
      // The condition of the current node has to be at the end because the subtrees have to be well-formed first.
      finalSubConds ++ conds
    }
  }

}
