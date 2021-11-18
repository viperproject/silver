package plugin.inline

import org.scalatest.FunSuite
import viper.silver.ast._
import viper.silver.plugin.standard.inline.InlineErrorChecker

class InlineErrorCheckerTest extends FunSuite with InlineErrorChecker with InlineTestFixture {

  test("findLoopBreakers should evaluate to an empty set given an empty set of predicates") {
    val program = parse("empty")

    assert(findLoopBreakers(predicateIds = Set(), program).isEmpty)
  }

  test("findLoopBreakers should evaluate to an empty set given a program with only non-recursive predicates") {
    val program = parse("assert-invariant")
    val predicateIds = Set() ++ program.predicates.map(_.name)

    assert(findLoopBreakers(predicateIds, program).isEmpty)
  }

  test("findLoopBreakers should evaluate to a set of recursive predicates given their ids") {
    val program = parse("recursive")
    val predicateIds = Set() ++ program.predicates.map(_.name)
    assert(findLoopBreakers(predicateIds, program) == predicateIds)
  }

  test("findLoopBreakers should evaluate to a set of recursive predicates given a number of recursive preds") {
    val program = parse("multi-rec")
    val predicateIds = Set() ++ program.predicates.map(_.name)
    assert(findLoopBreakers(predicateIds, program) == predicateIds)
  }

  test("findLoopBreakers should evaluate to a set containing a mutually-recursive predicates given their ids") {
    val program = parse("mutrec")
    val predicateIds = Set() ++ program.predicates.map(_.name)
    val result = findLoopBreakers(predicateIds, program)
    assert(result.size == 1 && result.forall(predicateIds(_)))
  }

  test("findLoopBreakers should pick a predicate with more in edges to try to reduce the number of loop-breakers") {
    val program = parse("aatree")
    val predicateIds = Set() ++ program.predicates.map(_.name)
    assert(findLoopBreakers(predicateIds, program) == Set("list"))
  }

}
