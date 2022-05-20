package viper.silver.plugin.standard.inline

import viper.silver.ast._
import viper.silver.ast.utility.Permissions.multiplyExpByPerm
import viper.silver.ast.utility.Simplifier.simplify
import viper.silver.ast.utility.ViperStrategy
import viper.silver.plugin.standard.inline.WrapPred._
import viper.silver.verifier.errors._

trait InlineRewrite {

  def poly_recur[X <: Node](x: X)(implicit recur: Node => Node): X = {
    recur(x).asInstanceOf[X]
  }

  def rewriteProgram(program: Program, inlinePreds: Seq[Predicate], assertFolds: Boolean): Program = {
    val predMap = InlinePredicateMap()
    val permDecl = LocalVarDecl("__perm__", Perm)()
    val permVar = permDecl.localVar
    val knownPositive = (p: LocalVar) => p == permVar
    var dummyN = 0
    val getDummyName = () => {dummyN += 1; s"__dummy__$dummyN"}
    val permPropagateStrategy = ViperStrategy.Slim({
      case acc: AccessPredicate => simplify(multiplyExpByPerm(acc, permVar))
    })
    val nop = Seqn(Seq(), Seq())()
    val strategy = ViperStrategyCustomTraverse.CustomContextTraverse[Set[String]]({
      case (acc@PredicateAccessPredicate(_, perm), ctxt, recur) if predMap.shouldRewrite(acc) =>
        (wrapPred(predMap.predicateBody(acc, ctxt, recur), perm, knownPositive), ctxt)
      case (u@Unfolding(acc, body), ctxt, recur) if predMap.shouldRewrite(acc) =>
        if (assertFolds) {
          (predMap.assertingIn(acc, recur(body).asInstanceOf[Exp], getDummyName())(u.pos, u.info, u.errT), ctxt)
        } else {
          (recur(body).asInstanceOf[Exp], ctxt)
        }
      case (u@Unfold(acc@PredicateAccessPredicate(_, perm)), ctxt, recur) if predMap.shouldRewrite(acc) =>
        val errT = ErrTrafo(err => UnfoldFailed(u, err.reason))
        if (assertFolds) {
          (Assert(wrapPredUnfold(predMap.predicateBody(acc, ctxt, recur), perm, knownPositive))(u.pos, u.info, errT), ctxt)
        } else {
          (nop, ctxt)
        }
      case (f@Fold(acc@PredicateAccessPredicate(_, perm)), ctxt, recur) if predMap.shouldRewrite(acc) =>
        val errT = ErrTrafo(err => FoldFailed(f, err.reason))
        if (assertFolds) {
          (Assert(wrapPredFold(predMap.predicateBodyNoErrT(acc, ctxt, recur), perm, knownPositive))(f.pos, f.info, errT), ctxt)
        } else {
          (nop, ctxt)
        }
      case (scope: Scope, ctxt, _) =>
        (scope, ctxt ++ scope.scopedDecls.map(_.name).toSet)
    }, Set())
    for (pred <- inlinePreds) {
      val pred2 = strategy.execute[Predicate](permPropagateStrategy.execute(pred))
      predMap.addPredicate(pred2, permDecl) // Modifies strategy so that pred can now be inlined
    }
    val prog2 = strategy.execute[Program](program)
    if (assertFolds) {
      prog2.copy(functions = prog2.functions ++ predMap.toUnfoldingFunctions)(prog2.pos, prog2.info, prog2.errT)
    } else {
      prog2
    }
  }
}
