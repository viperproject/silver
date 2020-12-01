package viper.silver.plugin.standard.inline

import scala.collection.mutable
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse

trait InlineRewrite {

  /**
    * Rewrites a method by expanding the predicates in its pre- and postconditions,
    * then by removing the corresponding unfold and fold statements in the body.
    * Note that we only remove unfolds for predicates from the preconditions,
    * and folds for predicates from the postconditions.
    * (I think that's how it works.)
    */
  def rewriteMethod(method: Method, program: Program): Method = {
    val (expandedPres, expandablePrePredsIds) = method.pres
      .map { expandPredicates(_, method, program) }
      .unzip
    val (expandedPosts, expandablePostPredsIds) = method.posts
      .map { expandPredicates(_, method, program) }
      .unzip
    val expandablePrePredIds = expandablePrePredsIds.fold(Set())(_ ++ _)
    val expandablePostPredIds = expandablePostPredsIds.fold(Set())(_ ++ _)
    val rewrittenBody = method.body
      .map { removeFoldUnfolds(_, expandablePrePredIds, expandablePostPredIds) }
    method.copy(body = rewrittenBody,
      pres = expandedPres,
      posts = expandedPosts,
    )(method.pos, method.info, method.errT)
  }

  /**
    * Expands all predicates to their bodies in given expression.
    *
    * @param expr The expression whose predicates will be expanded
    * @param method The method containing the expression, used to determine locally-scoped variables
    * @param program The program containing the expression, used to expand predicates
    * @return The expression with expanded predicates and a set of their names
    */
  private[this] def expandPredicates(expr: Exp, method: Method, program: Program): (Exp, Set[String]) = {
    // Forgive me deities of functional programming for I sin
    val expandablePredicates = mutable.Set[String]()
    val expandedExpr = ViperStrategy.Context[Set[String]]({
      case exp@(PredicateAccessPredicate(pred, _), ctxt) =>
        val body = pred.predicateBody(program, ctxt.c)
        val isInUnfolding = ctxt.parentOption.fold(false)(_.isInstanceOf[Unfolding])
        if (body.isDefined && !isInUnfolding) {
          expandablePredicates += pred.predicateName
          (body.get, ctxt)
        } else exp
      case (Unfolding(_, body), ctxt) => (body, ctxt)
      case (quant: QuantifiedExp, ctxt) =>
        (quant, ctxt.updateContext(ctxt.c ++ quant.scopedDecls.map { _.name }.toSet))
    }, method.scopedDecls.map { _.name }.toSet, Traverse.BottomUp)
      .execute[Exp](expr)
    (expandedExpr, expandablePredicates.toSet)
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
