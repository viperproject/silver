package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.{Exp, FieldAccessPredicate, PredicateAccessPredicate}
import viper.silver.ast.utility.rewriter.Traverse

trait PredicateExpansion {

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
