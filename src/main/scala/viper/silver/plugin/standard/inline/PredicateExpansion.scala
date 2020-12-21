package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast._
import viper.silver.ast.utility.rewriter.Traverse

trait PredicateExpansion {

  /**
    * Given the body of a predicate, find any access statements and thread the original permission value
    * into it. If the body is a None, evaluate to a None.
    *
    * @param maybeBody the body of a given predicate for which we want to thread the original permission value for.
    * @param originalPerm the original permission value used before inlining occurs.
    * @return the predicate body after threading the original permission value, if defined. Otherwise
    *         evaluate to None.
    */
  def propagatePermission(maybeBody: Option[Exp], originalPerm: Exp): Option[Exp] =
    maybeBody.map { body =>
      ViperStrategy.CustomContext[Exp]({
        case (predAcc@PredicateAccessPredicate(_, perm), outerPerm) =>
          val propagatedPerm = PermMul(perm, outerPerm)(perm.pos, perm.info, perm.errT)
          val modifiedPredAcc = predAcc.copy(
              perm = propagatedPerm
            )(predAcc.pos, predAcc.info, predAcc.errT)
          (modifiedPredAcc, propagatedPerm)
        case (fieldAcc@FieldAccessPredicate(_, perm), outerPerm) =>
          val propagatedPerm = PermMul(perm, outerPerm)(perm.pos, perm.info, perm.errT)
          val modifiedFieldAcc = fieldAcc.copy(
              perm = propagatedPerm
            )(fieldAcc.pos, fieldAcc.info, fieldAcc.errT)
          (modifiedFieldAcc, propagatedPerm)
      }, originalPerm, Traverse.TopDown).execute[Exp](body)
    }
}
