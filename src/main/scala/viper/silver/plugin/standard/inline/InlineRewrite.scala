package viper.silver.plugin.standard.inline

import scala.collection.mutable
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy

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
    method.copy(name = method.name,
        formalArgs = method.formalArgs,
        formalReturns = method.formalReturns,
        pres = expandedPres,
        posts = expandedPosts,
        body = rewrittenBody
      )(pos = method.pos, info = method.info, errT = method.errT)
  }

  /**
    * Expands all predicates to their bodies in given expression.
    * 
    * TODO: Expand only some specified predicates, not all
    *
    * @param expr The expression whose predicates will be expanded
    * @param method The method containing the expression, used to determine locally-scoped variables
    * @param program The program containing the expression, used to expand predicates
    * @return The expression with expanded predicates and a set of their names
    */
  private[this] def expandPredicates(expr: Exp, method: Method, program: Program): (Exp, Set[String]) = {
    // Forgive me deities of functional programming for I sin
    val expandablePredicates = mutable.Set[String]()
    val expandedExpr = ViperStrategy.CustomContext[Set[String]]({
      case (expr, args) => expr match {
        case pred: PredicateAccess =>
          val body = pred.predicateBody(program, args)
          if (body.isDefined) expandablePredicates += pred.predicateName
          (body.getOrElse(pred), args)
        case quant: QuantifiedExp => ???
          // TODO: Continue traversing quant, but with context (args ++ quant.scopedDecls.map { _.name }.toSet)
      }
    }, method.scopedDecls.map { _.name }.toSet)
      // .recurseFunc(???) // TODO: Do we need to call this first?
      .execute(expr)
    (expandedExpr, expandablePredicates.toSet)
  }

  /**
    * Removes given predicate unfolds and folds from statement.
    * 
    * TODO: How to specify to Slim that the type to traverse is Stmt in general, not only Seqn?
    *
    * @param stmt A Seqn whose statments will be traversed
    * @param unfoldPreds A set of the string names of the precondition predicates to not unfold
    * @param foldPreds A set of the string names of the postcondition predicates to not fold
    * @return The Seqn with all above unfolds and folds removed
    */
  private[this] def removeFoldUnfolds(stmts: Seqn, unfoldPreds: Set[String], foldPreds: Set[String]): Seqn = {
    val noop: Stmt = Assert(TrueLit.apply()())() // TODO: Is there some other way of getting rid of a statement?
    ViperStrategy.Slim({
      case fold@Fold(PredicateAccessPredicate(PredicateAccess(_, name), _)) =>
        if (foldPreds(name)) noop else fold
      case unfold@Unfold(PredicateAccessPredicate(PredicateAccess(_, name), _)) =>
        if (unfoldPreds(name)) noop else unfold
    }) // .recurseFunc(???) // TODO: Do we need to call this first?
      .execute(stmts)
  }
}
