package viper.silver.plugin.standard.inline

import viper.silver.ast._
import viper.silver.ast.utility.{QuantifiedPermissions, ViperStrategy}
import viper.silver.plugin.SilverPlugin
import viper.silver.plugin.standard.inline.WrapPred._
import viper.silver.verifier.ConsistencyError
import viper.silver.verifier.errors._

trait InlineRewrite extends SilverPlugin {

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
    val state = InlinePredicateState()
    val trigMan = new TriggerManager(program, inlinePreds, state.names)
    val knownPositive = (p: LocalVar) => p == state.permVar
    val permPropagateStrategy = ViperStrategy.Slim({
      case acc: AccessPredicate => multiplyExpByPerm(acc, state.permVar)
    })
    val strategy = ViperStrategyCustomTraverse.CustomContextTraverse[Set[String]]({
      case (acc@PredicateAccessPredicate(_, perm), ctxt, recur) if state.shouldRewrite(acc) =>
        (wrapPred(state.predicateBody(acc, ctxt, recur), perm, knownPositive), ctxt)
      case (u@Unfolding(acc, body), ctxt, recur) if state.shouldRewrite(acc) =>
        val res = if (assertFolds) {
          state.assertingIn(acc, recur(body).asInstanceOf[Exp])(u.pos, u.info, u.errT)
        } else {
          recur(body).asInstanceOf[Exp]
        }
        (trigMan.wrap(acc, res), ctxt)
      case (u@Unfold(acc@PredicateAccessPredicate(_, perm)), ctxt, recur) if state.shouldRewrite(acc) =>
        val errT = ErrTrafo(err => UnfoldFailed(u, err.reason))
        val res = if (assertFolds) {
          wrapPredUnfold(state.predicateBody(acc, ctxt, recur), perm, knownPositive)
        } else {
          TrueLit()()
        }
        (Assert(trigMan.wrap(acc, res))(u.pos, u.info, errT), ctxt)
      case (f@Fold(acc@PredicateAccessPredicate(_, perm)), ctxt, recur) if state.shouldRewrite(acc) =>
        val errT = ErrTrafo(err => FoldFailed(f, err.reason))
        val res = if (assertFolds) {
          wrapPredFold(state.predicateBodyNoErrT(acc, ctxt, recur), perm, knownPositive)
        } else {
          TrueLit()()
        }
        (Assert(trigMan.wrap(acc, res))(f.pos, f.info, errT), ctxt)
      case (p@CurrentPerm(PredicateAccess(_, _)), ctxt, _) =>
        reportError(ConsistencyError("Inlined predicates cannot be used in perm expressions", p.pos))
        (p, ctxt)
      // Ugly hack needed since foralls are desugared before we get a chance to run
      case (fa@Forall(_, _, exp), ctxt, recur) =>
        val faTrig = fa.autoTrigger
        val fa2 = faTrig.copy(exp = recur(exp).asInstanceOf[Exp], triggers = trigMan.mapTriggers(faTrig.triggers))(fa.pos, faTrig.info, fa.errT)
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
      state.addPredicate(pred2) // Modifies strategy so that pred can now be inlined
    }
    val prog2 = strategy.execute[Program](program)
    val prog3 = prog2.copy(domains = prog2.domains.prependedAll(trigMan.intoDomain()))(prog2.pos, prog2.info, prog2.errT)
    if (assertFolds) {
      prog3.copy(functions = prog3.functions ++ state.toUnfoldingFunctions)(prog3.pos, prog3.info, prog3.errT)
    } else {
      prog3
    }
  }
}
