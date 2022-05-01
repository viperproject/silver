package viper.silver.plugin.standard.inline

import viper.silver.ast.{And, Exp, FractionalPerm, FullPerm, Implies, IntLit, LocalVar, NoPerm, PermGeCmp, PermGtCmp}

object WrapPred {
  private def isPositive(perm: Exp, knowPositive: LocalVar => Boolean): Boolean = perm match {
    case FullPerm() => true
    case FractionalPerm(IntLit(i1), IntLit(i2)) => i1 > 0 && i2 > 0
    case l: LocalVar if knowPositive(l) => true
    case _ => false
  }

  def wrapPred(expandedExpr: Exp, perm: Exp, knowPositive: LocalVar => Boolean = _ => false): Exp = {
    if (isPositive(perm, knowPositive)) {
      return expandedExpr
    }
    And(PermGeCmp(perm, NoPerm()())(), Implies(PermGtCmp(perm, NoPerm()())(), expandedExpr)())()
  }
  def wrapPredUnfold(expandedExpr: Exp, perm: Exp, knowPositive: LocalVar => Boolean = _ => false): Exp = wrapPred(expandedExpr, perm, knowPositive)
  def wrapPredFold(expandedExpr: Exp, perm: Exp, knowPositive: LocalVar => Boolean = _ => false): Exp = {
    if (isPositive(perm, knowPositive)) {
      return expandedExpr
    }
    And(PermGtCmp(perm, NoPerm()())(), expandedExpr)()
  }
}
