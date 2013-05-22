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

  def proofObligations(e: Exp): Seq[Exp] = e.reduceTree[Seq[Exp]] { (n: Node, subConds: Seq[Seq[Exp]]) =>
    val p = n match {
      case n: Positioned => n.pos
      case _ => NoPosition
    }
    val conds = n match {
      case f@FieldAccess(rcv, _) => List(NeCmp(rcv, NullLit()(p))(p), FieldAccessPredicate(f, WildcardPerm()(p))(p))
      case f: FuncApp => f.pres
      case Div(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
      case Mod(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
      case _ => Nil
    }
    val nonTrivialSubConds: Seq[Exp] = subConds.flatten.filter { _ != TrueLit()() }
    // The condition has to be at the end because the subtrees have to be well-formed first.
    nonTrivialSubConds ++ conds
  }

}
