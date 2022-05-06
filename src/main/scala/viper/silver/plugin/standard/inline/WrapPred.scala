package viper.silver.plugin.standard.inline

import viper.silver.ast._
import viper.silver.verifier.reasons.NegativePermission

object WrapPred {
  private def isPositive(perm: Exp, knowPositive: LocalVar => Boolean): Boolean = perm match {
    case FullPerm() => true
    case FractionalPerm(IntLit(i1), IntLit(i2)) => i1 > 0 && i2 > 0
    case PermDiv(p, IntLit(i)) => isPositive(p, knowPositive) && i > 0
    case PermMul(p1, p2) => isPositive(p1, knowPositive) && isPositive(p2, knowPositive)
    case l: LocalVar if knowPositive(l) => true
    case _ => false
  }

  private def checkNonNegative(perm: Exp): Exp = {
    val errT = Trafos(Nil, List({_ => NegativePermission(perm)}), Some(perm))
    PermGeCmp(perm, NoPerm()())(errT = errT)
  }

  def wrapPred(expandedExpr: Exp, perm: Exp, knowPositive: LocalVar => Boolean = _ => false): Exp = {
    if (isPositive(perm, knowPositive)) {
      return expandedExpr
    }
    And(checkNonNegative(perm), Implies(PermGtCmp(perm, NoPerm()())(), expandedExpr)(errT = expandedExpr.errT))()
  }
  def wrapPredUnfold(expandedExpr: Exp, perm: Exp, knowPositive: LocalVar => Boolean = _ => false): Exp = wrapPred(expandedExpr, perm, knowPositive)
  def wrapPredFold(expandedExpr: Exp, perm: Exp, knowPositive: LocalVar => Boolean = _ => false): Exp = {
    if (isPositive(perm, knowPositive)) {
      return expandedExpr
    }
    And(checkNonNegative(perm), expandedExpr)()
  }
}
