package viper.silver.plugin.standard.inline

import scala.collection.mutable
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.{ContextC, Traverse}

trait InlineRewrite extends PredicateExpansion {

  private type Context = ContextC[Node, Set[String]]

  def inlinePredicates(method: Method, program: Program, cond: String => Boolean): Method = {
    val expandedPres = method.pres.map(expandPredicates(_, method, program, cond))
    val expandedPosts = method.posts.map(expandPredicates(_, method, program, cond))
    val rewrittenBody = method.body.map { ss =>
      ss.copy(
        ss = ss.ss.map(expandInhaleStatement(_, method, program, cond))
      )(pos = ss.pos, info = ss.info, errT = ss.errT)
    }
    method.copy(
      body = rewrittenBody,
      pres = expandedPres,
      posts = expandedPosts
    )(method.pos, method.info, method.errT)
  }

  def rewriteMethod(method: Method, cond: String => Boolean): Method = {
    val rewrittenPres = method.pres.map { removeUnfoldings(_, cond) }
    val rewrittenPosts = method.posts.map { removeUnfoldings(_, cond) }
    val rewrittenBody = method.body.map { removeFoldUnfolds(_, cond) }
    method.copy(body = rewrittenBody,
      pres = rewrittenPres,
      posts = rewrittenPosts,
    )(method.pos, method.info, method.errT)
  }

  /**
    * Expands all predicates to their bodies in given expression.
    *
    * @param expr The expression whose predicates will be expanded
    * @param method The method containing the expression, used to determine locally-scoped variables
    * @param program The program containing the expression, used to expand predicates
    * @param cond The predicate (Scala) that the predicates (Viper) must satisfy
    * @return The expression with expanded predicates and the expandable precondition and postcondition predicates
    */
  private[this] def expandPredicates(expr: Exp, method: Method, program: Program, cond: String => Boolean): Exp = {
    val expandablePredicates = mutable.Set[String]()
    ViperStrategy.Context[Set[String]]({
      case exp@(PredicateAccessPredicate(pred, perm), ctxt) =>
        val isInUnfolding = isWithinUnfolding(ctxt)
        if (cond(pred.predicateName) && !isInUnfolding) {
          expandablePredicates += pred.predicateName
          val optPredBody = pred.predicateBody(program, ctxt.c)
          (propagatePermission(optPredBody, perm).get, ctxt)
        } else exp
      case (scope: Scope, ctxt) =>
        (scope, ctxt.updateContext(ctxt.c ++ scope.scopedDecls.map(_.name).toSet))
    }, method.scopedDecls.map(_.name).toSet, Traverse.TopDown)
      .execute[Exp](expr)
  }

  /**
    * Given an inhale statement, look within it for any predicate accesses. If found, return the same inhale statement
    * with the expanded value of the predicate.
    *
    * @param stmt The statement containing the inhale statement we wish to expana.
    * @param method The method containing the inhale statement we wish to expand.
    * @param program The Viper program for which we perform this expansion.
    * @param cond The condition a predicate must satisfy to be expanded within an inhale statement.
    * @return The expanded inhale statement.
    */
  private[this] def expandInhaleStatement(stmt: Stmt, method: Method, program: Program, cond: String => Boolean): Stmt =
    ViperStrategy.Context[Set[String]]({
      case (inhaleStmt: Inhale, ctxt) =>
        val expandedExpr = expandInhaleContainedExpr(inhaleStmt.exp, method, program, cond)
        val expandedInhaleStmt =
          inhaleStmt.copy(exp = expandedExpr)(pos = inhaleStmt.pos, info = inhaleStmt.info, errT = inhaleStmt.errT)
        (expandedInhaleStmt, ctxt)
    }, method.scopedDecls.map(_.name).toSet, Traverse.TopDown).execute[Stmt](stmt)

  /**
    * Given a predicate access or a predicate access predicate in the context of an inhale statement,
    * expand the expression and produce it as a value.
    *
    * @param expr The expression (likely a PredicateAccess/PredicateAccessPredicate) that we want to expand.
    * @param method The method in which this expansion occurs.
    * @param program The Viper program for which we perform this expansion.
    * @param cond The condition a predicate must satisfy to be expanded within an inhale statement.
    * @return The expanded expression.
    */
  private[this] def expandInhaleContainedExpr(expr: Exp, method: Method, program: Program, cond: String => Boolean): Exp  =
    ViperStrategy.Context[Set[String]]({
      case exp @ (PredicateAccessPredicate(pred, perm), ctxt) =>
        val isInUnfolding = isWithinUnfolding(ctxt)
        if (cond(pred.predicateName) && !isInUnfolding) {
          val maybePredBody = pred.predicateBody(program, ctxt.c)
          (propagatePermission(maybePredBody, perm).get, ctxt)
        } else exp
      case (newScope: Scope, ctxt) =>
        (newScope, ctxt.updateContext(ctxt.c ++ newScope.scopedDecls.map(_.name).toSet))
    }, method.scopedDecls.map(_.name).toSet, Traverse.TopDown).execute[Exp](expr)


  /**
    * Replaces unfolding expressions by their bodies if the unfolded predicate had been expanded
    *
    * @param expr The expression whose unfoldings may be substituted
    * @param cond The condition a predicate must satisfy to be un-unfolding-ed
    * @return The expression with unfoldings possibly substituted
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
    * @param stmts A Seqn whose statements will be traversed
    * @param cond The condition a predicate must satisfy to no longer require (un)folding
    * @return The Seqn with all above unfolds and folds removed
    */
  private[this] def removeFoldUnfolds(stmts: Seqn, cond: String => Boolean): Seqn = {
    ViperStrategy.Slim({
      case seqn@Seqn(ss, _) =>
        seqn.copy(ss = ss.filterNot {
          case Fold(PredicateAccessPredicate(PredicateAccess(_, name), _)) => cond(name)
          case Unfold(PredicateAccessPredicate(PredicateAccess(_, name), _)) => cond(name)
          case _ => false
        })(seqn.pos, seqn.info, seqn.errT)
    }, Traverse.BottomUp).execute[Seqn](stmts)
  }

  private[this] def isWithinUnfolding(ctxt: Context): Boolean = {
    ctxt.parentOption.exists {
      case _: Unfolding => true
      case _ => false
    }
  }
}
