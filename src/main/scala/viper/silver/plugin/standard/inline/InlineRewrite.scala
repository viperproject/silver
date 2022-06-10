package viper.silver.plugin.standard.inline

import viper.silver.ast._
import viper.silver.ast.utility.{QuantifiedPermissions, ViperStrategy}
import viper.silver.plugin.standard.inline.WrapPred._
import viper.silver.verifier.errors._

trait InlineRewrite {

  def poly_recur[X <: Node](x: X)(implicit recur: Node => Node): X = {
    recur(x).asInstanceOf[X]
  }

  def multiplyPermByPerm(p: Exp, permVar: LocalVar): Exp = p match {
    case FullPerm() => permVar.withMeta(p.pos, p.info, p.errT)
    case WildcardPerm() => WildcardPerm()(p.pos, p.info, p.errT)
    case _ => PermMul(p, permVar)(p.pos, p.info, p.errT)
  }

  def multiplyExpByPerm(acc: AccessPredicate, permVar: LocalVar): AccessPredicate = acc match {
    case fa@FieldAccessPredicate(loc,p) => FieldAccessPredicate(loc,multiplyPermByPerm(p, permVar))(fa.pos,fa.info)
    case pa@PredicateAccessPredicate(loc,p) => PredicateAccessPredicate(loc, multiplyPermByPerm(p, permVar))(pa.pos,pa.info)
    case _: MagicWand => sys.error("Cannot yet permission-scale magic wands")
  }

  def rewriteProgram(program: Program, inlinePreds: Seq[Predicate], assertFolds: Boolean): Program = {
    val predMap = InlinePredicateState()
    val permDecl = LocalVarDecl("__perm__", Perm)()
    val permVar = permDecl.localVar
    val knownPositive = (p: LocalVar) => p == permVar
    var dummyN = 0
    val getDummyName = () => {dummyN += 1; s"__dummy__$dummyN"}
    val permPropagateStrategy = ViperStrategy.Slim({
      case acc: AccessPredicate => multiplyExpByPerm(acc, permVar)
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
      // Ugly hack needed since foralls are desugared before we get a chance to run
      case (fa@Forall(_, _, exp), ctxt, recur) =>
        val faTrig = fa.autoTrigger
        val fa2 = faTrig.copy(exp = recur(exp).asInstanceOf[Exp])(fa.pos, faTrig.info, fa.errT)
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
    if (assertFolds) {
      prog2.copy(functions = prog2.functions ++ predMap.toUnfoldingFunctions)(prog2.pos, prog2.info, prog2.errT)
    } else {
      prog2
    }
  }
}
