package plugin.inline

import org.scalatest.FunSuite
import viper.silver.ast.{Add, FullPerm, IntLit, Predicate, PredicateAccess, PredicateAccessPredicate, Program}
import viper.silver.plugin.standard.inline.InlineErrorChecker

class InlineErrorCheckerTest extends FunSuite with InlineErrorChecker with InlineTestFixture {

  test("checkRecursive should evaluate to an empty set given an empty set of predicates") {
    val program = programCopy()

    checkRecursive(predicateIds = Set(), program).isEmpty
  }

  test("checkRecursive should evaluate to an empty set given a non-recursive predicate") {
    val predId = "nonrec"
    val maybeNonRecursiveBody = Some(Add(IntLit(69)(), IntLit(420)())())
    val nonRecursivePred = Predicate(predId, formalArgs = Seq(), body = maybeNonRecursiveBody)()
    val program = programCopy(predicates = Seq(nonRecursivePred))

    checkRecursive(predicateIds = Set(predId), program).isEmpty
  }

  test("checkRecursive should evaluate to a set of recursive predicates given their ids") {
    val predId = "rec"
    val maybeRecursiveBody = Some(PredicateAccessPredicate(PredicateAccess(Seq(), predId)(), FullPerm.apply()())())
    val recursivePred = Predicate(predId, formalArgs = Seq(), body = maybeRecursiveBody)()
    val program = programCopy(predicates = Seq(recursivePred))

    val result = checkRecursive(predicateIds = Set(predId), program)
    result.size == 1 && result.forall {
      case Predicate(name, _, _) => name == predId
      case _ => false
    }
  }
}
