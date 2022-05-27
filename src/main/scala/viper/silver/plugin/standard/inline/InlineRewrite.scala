package viper.silver.plugin.standard.inline

import viper.silver.ast._
import viper.silver.ast.utility.Permissions.multiplyExpByPerm
import viper.silver.ast.utility.Simplifier.simplify
import viper.silver.ast.utility.{QuantifiedPermissions, ViperStrategy}
import viper.silver.frontend.{ApproximateIPS, AssertingIPS, DefaultIPS, InlinePredicateStrategy}
import viper.silver.plugin.standard.inline.WrapPred._
import viper.silver.verifier.errors._

trait InlineRewrite {

  def rewriteProgram(program: Program, inlinePreds: Seq[Predicate], stat: InlinePredicateStrategy): Program = {
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
      case (u@Unfolding(acc@PredicateAccessPredicate(_, perm), body), ctxt, recur) if predMap.shouldRewrite(acc) =>
        val rbody = recur(body).asInstanceOf[Exp]
        if (stat == ApproximateIPS) {
          (rbody, ctxt)
        } else if (stat == AssertingIPS) {
          val res = Asserting(wrapPredUnfold(predMap.predicateBody(acc, ctxt, recur), perm, knownPositive), rbody)(u.pos, u.info)
          (res, ctxt)
        } else {
          (predMap.assertingIn(acc, rbody, getDummyName())(u.pos, u.info, u.errT), ctxt)
        }
      case (u@Unfold(acc@PredicateAccessPredicate(_, perm)), ctxt, recur) if predMap.shouldRewrite(acc) =>
        val errT = ErrTrafo(err => UnfoldFailed(u, err.reason))
        if (stat != ApproximateIPS) {
          (Assert(wrapPredUnfold(predMap.predicateBody(acc, ctxt, recur), perm, knownPositive))(u.pos, u.info, errT), ctxt)
        } else {
          (nop, ctxt)
        }
      case (f@Fold(acc@PredicateAccessPredicate(_, perm)), ctxt, recur) if predMap.shouldRewrite(acc) =>
        val errT = ErrTrafo(err => FoldFailed(f, err.reason))
        if (stat != ApproximateIPS) {
          (Assert(wrapPredFold(predMap.predicateBodyNoErrT(acc, ctxt, recur), perm, knownPositive))(f.pos, f.info, errT), ctxt)
        } else {
          (nop, ctxt)
        }
      // Hack needed since foralls are desugared before we get a chance to run
      case (fa@Forall(_, _, exp), ctxt, recur) =>
        val fa2 = fa.copy(exp = recur(exp).asInstanceOf[Exp])(fa.pos, fa.info, fa.errT)
        val fa3 = if (fa == fa2) {
          fa
        } else {
          val desugaredForalls = QuantifiedPermissions.desugarSourceQuantifiedPermissionSyntax(fa2)
          desugaredForalls.tail.foldLeft(desugaredForalls.head: Exp)((conjuncts, forall) => And(conjuncts, forall)(fa2.pos, fa2.info, fa2.errT))
        }
        (fa3, ctxt)
      case (scope: Scope, ctxt, _) =>
        (scope, ctxt ++ scope.scopedDecls.map(_.name).toSet)
    }, Set())
    for (pred <- inlinePreds) {
      val pred2 = strategy.execute[Predicate](permPropagateStrategy.execute(pred))
      predMap.addPredicate(pred2, permDecl) // Modifies strategy so that pred can now be inlined
    }
    val prog2 = strategy.execute[Program](program)
    if (stat == DefaultIPS) {
      prog2.copy(functions = prog2.functions ++ predMap.toUnfoldingFunctions)(prog2.pos, prog2.info, prog2.errT)
    } else {
      prog2
    }
  }
}
