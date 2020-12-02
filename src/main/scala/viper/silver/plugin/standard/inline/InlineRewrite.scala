package viper.silver.plugin.standard.inline

import scala.collection.mutable
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.utility.rewriter.StrategyBuilder

trait InlineRewrite {

  def getPrePostPredIds(method: Method, program: Program): (Set[String], Set[String]) = {
    val expandablePrePredIds = method.pres.map { expandablePredicates(_, method, program) }.flatten.toSet
    val expandablePostPredsIds = method.posts.map { expandablePredicates(_, method, program) }.flatten.toSet
    (expandablePrePredIds, expandablePostPredsIds)
  }

  def inlinePredicates(method: Method, program: Program, prePredIds: Set[String], postPredIds: Set[String]): Method = {
    val expandedPres = method.pres.map { expandPredicates(_, method, program, prePredIds) }
    val expandedPosts = method.posts.map { expandPredicates(_, method, program, postPredIds) }
    method.copy(
      pres = expandedPres,
      posts = expandedPosts
    )(method.pos, method.info, method.errT)
  }

  def rewriteMethod(method: Method, program: Program, prePredIds: Set[String], postPredIds: Set[String]): Method = {
    val rewrittenPres = method.pres.map { removeUnfoldings(_, prePredIds) }
    val rewrittenPosts = method.posts.map { removeUnfoldings(_, postPredIds) }
    val rewrittenBody = method.body.map { removeFoldUnfolds(_, prePredIds, postPredIds) }
    method.copy(body = rewrittenBody,
      pres = rewrittenPres,
      posts = rewrittenPosts,
    )(method.pos, method.info, method.errT)
  }

  /**
    * Returns a set of the names of the predicates that can be expanded into their bodies.
    *
    * @param expr The expression to check for predicates
    * @param method The method containing the expression, used to determine locally-scoped variables
    * @param program The program containing the expression, used to get predicate bodies
    * @return A set of the names of the expandable predicates
    */
  private[this] def expandablePredicates(expr: Exp, method: Method, program: Program): Set[String] = {
    // Forgive me deities of functional programming for I sin
    val expandablePredicates = mutable.Set[String]()
    StrategyBuilder.ContextVisitor[Node, Set[String]]({
      case exp@(PredicateAccessPredicate(pred, _), ctxt) =>
        // TODO: Check for `inline` modifier
        if (pred.predicateBody(program, ctxt.c).isDefined) {
          expandablePredicates += pred.predicateName
        }
        ctxt
      case (quant: QuantifiedExp, ctxt) =>
        ctxt.updateContext(ctxt.c ++ quant.scopedDecls.map { _.name }.toSet)
      case (_, ctxt) => ctxt
    }, method.scopedDecls.map { _.name }.toSet).execute[Exp](expr)
    expandablePredicates.toSet
  }

  /**
    * Expands all predicates to their bodies in given expression.
    *
    * @param expr The expression whose predicates will be expanded
    * @param method The method containing the expression, used to determine locally-scoped variables
    * @param program The program containing the expression, used to expand predicates
    * @param preds The predicates that we are allowed to expand
    * @return The expression with expanded predicates
    */
  private[this] def expandPredicates(expr: Exp, method: Method, program: Program, preds: Set[String]): Exp = {
    ViperStrategy.Context[Set[String]]({
      case exp@(PredicateAccessPredicate(pred, _), ctxt) =>
        val isInUnfolding = ctxt.parentOption.exists({_.isInstanceOf[Unfolding]})
        if (preds(pred.predicateName) && !isInUnfolding) {
          (pred.predicateBody(program, ctxt.c).get, ctxt)
        } else exp
      case (quant: QuantifiedExp, ctxt) =>
        (quant, ctxt.updateContext(ctxt.c ++ quant.scopedDecls.map { _.name }.toSet))
    }, method.scopedDecls.map { _.name }.toSet, Traverse.TopDown)
      .execute[Exp](expr)
  }

  /**
    * Replaces unfolding expressions by their bodies if the unfolded predicate had been expanded
    *
    * @param expr The expression whose unfoldings may be substituted
    * @param preds A set of the string names of the predicates that have been expanded
    * @return The expression with unfoldings possibly substituted
    */
  private[this] def removeUnfoldings(expr: Exp, preds: Set[String]): Exp = {
    ViperStrategy.Slim({
      case unfolding@Unfolding(PredicateAccessPredicate(PredicateAccess(_, name), _), body) =>
        if (preds(name)) body else unfolding
    }, Traverse.BottomUp).execute[Exp](expr)
  }

  /**
    * Removes given predicate unfolds and folds from statement.
    *
    * @param stmt A Seqn whose statments will be traversed
    * @param unfoldPreds A set of the string names of the precondition predicates to not unfold
    * @param foldPreds A set of the string names of the postcondition predicates to not fold
    * @return The Seqn with all above unfolds and folds removed
    */
  private[this] def removeFoldUnfolds(stmts: Seqn, unfoldPreds: Set[String], foldPreds: Set[String]): Seqn = {
    ViperStrategy.Slim({
      case seqn@Seqn(ss, scopedDecls) =>
        seqn.copy(ss = ss.filter {
          case Fold(PredicateAccessPredicate(PredicateAccess(_, name), _)) => !foldPreds(name)
          case Unfold(PredicateAccessPredicate(PredicateAccess(_, name), _)) => !unfoldPreds(name)
          case _ => true
        })(seqn.pos, seqn.info, seqn.errT)
    }, Traverse.BottomUp).execute[Seqn](stmts)
  }
}
