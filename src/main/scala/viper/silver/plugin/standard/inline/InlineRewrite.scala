package viper.silver.plugin.standard.inline

import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse

trait InlineRewrite extends PredicateExpansion {
  def inlinePredicates(method: Method, program: Program, cond: String => Boolean): Method = {
    val expandedPres = method.pres.map(expandExpression(_, method, program, cond))
    val expandedPosts = method.posts.map(expandExpression(_, method, program, cond))
    val rewrittenBody = method.body.map(expandStatements(_, method, program, cond))
    method.copy(
      body = rewrittenBody,
      pres = expandedPres,
      posts = expandedPosts
    )(method.pos, method.info, method.errT)
  }

  def rewriteMethod(method: Method, cond: String => Boolean): Method = {
    val rewrittenBody = method.body.map(removeFoldUnfolds(_, cond))
    method.copy(body = rewrittenBody)(method.pos, method.info, method.errT)
  }

  /**
    * Expands all predicates to their bodies in given expression.
    *
    * @param expr The expression whose predicates will be expanded.
    * @param method The method containing the expression, used to determine locally-scoped variables.
    * @param program The program containing the expression, used to expand predicates.
    * @param cond The predicate (Scala) that the predicates (Viper) must satisfy.
    * @return The expression with expanded predicates and the expandable precondition and postcondition predicates.
    */
  private[this] def expandExpression(expr: Exp, method: Method, program: Program, cond: String => Boolean): Exp = {
    val noUnfoldingExpr = removeUnfoldings(expr, cond)
    ViperStrategy.CustomContext[Set[String]]({
      case (expr@PredicateAccessPredicate(pred, perm), ctxt) =>
        if (cond(pred.predicateName)) {
          val optPredBody = pred.predicateBody(program, ctxt)
          (propagatePermission(optPredBody, perm).get, ctxt)
        } else (expr, ctxt)
      case (scope: Scope, ctxt) =>
        (scope, ctxt ++ scope.scopedDecls.map(_.name).toSet)
    }, method.scopedDecls.map(_.name).toSet, Traverse.TopDown).execute[Exp](noUnfoldingExpr)
  }

  /**
    * Given an inhale, exhale, or assert statement, or a while loop invariant,
    * look within it for any predicate accesses.
    * If found, return the same statement with the expanded body of the predicate.
    *
    * @param stmts A Seqn whose statements will be traversed.
    * @param method The method containing the inhale statement we wish to expand.
    * @param program The Viper program for which we perform this expansion.
    * @param cond The condition a predicate must satisfy to be expanded within an inhale statement.
    * @return The Seqn with all inhale, exhale, assert, and while loop statements expanded.
    */
  private[this] def expandStatements(stmts: Seqn, method: Method, program: Program, cond: String => Boolean): Seqn =
    ViperStrategy.Slim({
      case inhale@Inhale(expr) =>
        val expandedExpr = expandExpression(expr, method, program, cond)
        inhale.copy(expandedExpr)(pos = inhale.pos, info = inhale.info, errT = inhale.errT)
      case exhale@Exhale(expr) =>
        val expandedExpr = expandExpression(expr, method, program, cond)
        exhale.copy(expandedExpr)(pos = exhale.pos, info = exhale.info, errT = exhale.errT)
      case assert@Assert(expr) =>
        val expandedExpr = expandExpression(expr, method, program, cond)
        assert.copy(expandedExpr)(pos = assert.pos, info = assert.info, errT = assert.errT)
      case loop@While(_, invs, _) =>
        val expandedInvs = invs.map(expandExpression(_, method, program, cond))
        loop.copy(invs = expandedInvs)(pos = loop.pos, info = loop.info, errT = loop.errT)
    }, Traverse.TopDown).execute[Seqn](stmts)

  /**
    * Replaces unfolding expressions by their bodies if the unfolded predicate had been expanded
    *
    * @param expr The expression whose unfoldings may be substituted.
    * @param cond The condition a predicate must satisfy to be un-unfolding-ed.
    * @return The expression with unfoldings possibly substituted.
    */
  private[this] def removeUnfoldings(expr: Exp, cond: String => Boolean): Exp = {
    ViperStrategy.Slim({
      case unfolding@Unfolding(PredicateAccessPredicate(PredicateAccess(_, name), _), body) =>
        if (cond(name)) body else unfolding
    }, Traverse.BottomUp).execute[Exp](expr)
  }

  /**
    * Removes given predicate unfolds and folds from statement.
    *
    * @param stmts A Seqn whose statements will be traversed.
    * @param cond The condition a predicate must satisfy to no longer require (un)folding.
    * @return The Seqn with all above unfolds and folds removed.
    */
  private[this] def removeFoldUnfolds(stmts: Seqn, cond: String => Boolean): Seqn = {
    ViperStrategy.Slim({
      case seqn@Seqn(ss, _) =>
        seqn.copy(ss = ss.filterNot {
          case Fold(PredicateAccessPredicate(PredicateAccess(_, name), _)) => cond(name)
          case Unfold(PredicateAccessPredicate(PredicateAccess(_, name), _)) => cond(name)
          case _ => false
        })(seqn.pos, seqn.info, seqn.errT)
    }, Traverse.TopDown).execute[Seqn](stmts)
  }
}
