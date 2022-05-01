package viper.silver.plugin.standard.inline

import viper.silver.ast.{And, Exp, Implies, NoPerm, PermGeCmp, PermGtCmp}

object WrapPred {
  def wrapPred(expandedExpr: Exp, perm: Exp): Exp = And(PermGeCmp(perm, NoPerm()())(), Implies(PermGtCmp(perm, NoPerm()())(), expandedExpr)())()
  def wrapPredUnfold(expandedExpr: Exp, perm: Exp): Exp = wrapPred(expandedExpr, perm)
  def wrapPredFold(expandedExpr: Exp, perm: Exp): Exp = And(PermGtCmp(perm, NoPerm()())(), expandedExpr)()
}
