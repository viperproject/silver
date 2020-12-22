package plugin.inline

import org.scalatest.FunSuite
import viper.silver.ast._
import viper.silver.plugin.standard.inline.PredicateExpansion

class PredicateExpansionTest extends FunSuite with PredicateExpansion {

  test("propagatePermission should evaluate to None if the body of the predicate is None") {
    val maybePredBody = None
    val perm = FullPerm()()

    assert(propagatePermission(maybePredBody, perm).isEmpty)
  }
}
