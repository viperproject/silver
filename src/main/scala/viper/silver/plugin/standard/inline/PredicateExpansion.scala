package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.{Exp, FieldAccessPredicate, PredicateAccessPredicate}
import viper.silver.ast.utility.rewriter.Traverse

trait PredicateExpansion {

  /**
    * Given the body of a predicate, find any access statements and thread the original permission value
    * into it. If the body is a None, evaluate to a None.
    *
    * @param maybeBody the body of a given predicate for which we want to thread the original permission value for.
    * @param originalPerm the original permission value used before inlining occurs.
    * @return the predicate body after threading the orignal permission value, if defined. Otherwise
    *         evaluate to None.
    */
  def propagatePermission(maybeBody: Option[Exp], originalPerm: Exp): Option[Exp] =
    maybeBody.map { body =>
      ViperStrategy.Slim({
        case predAccessPred: PredicateAccessPredicate =>
          predAccessPred.copy(
            loc = predAccessPred.loc,
            perm = originalPerm
          )(pos = predAccessPred.pos, info = predAccessPred.info, errT = predAccessPred.errT)
        case fieldAccessPred: FieldAccessPredicate =>
          fieldAccessPred.copy(
            loc = fieldAccessPred.loc,
            perm = originalPerm
          )(pos = fieldAccessPred.pos, info = fieldAccessPred.info, errT = fieldAccessPred.errT)
      }, Traverse.TopDown).execute[Exp](body)
    }
}
