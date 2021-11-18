package plugin.inline

import org.scalatest.FunSuite
import viper.silver.ast._
import viper.silver.plugin.standard.inline.InlineErrorChecker

class InlineErrorCheckerTest extends FunSuite with InlineErrorChecker with InlineTestFixture {

  test("findLoopBreakers should evaluate to an empty set given an empty set of predicates") {
    val program = programCopy()

    assert(findLoopBreakers(predicateIds = Set(), program).isEmpty)
  }

  test("findLoopBreakers should evaluate to an empty set given a non-recursive predicate") {
    val predId = "nonrec"
    val maybeNonRecursiveBody = Some(Add(IntLit(69)(), IntLit(420)())())
    val nonRecursivePred = Predicate(predId, formalArgs = Seq(), body = maybeNonRecursiveBody)()
    val program = programCopy(predicates = Seq(nonRecursivePred))

    assert(findLoopBreakers(predicateIds = Set(predId), program).isEmpty)
  }

  test("findLoopBreakers should evaluate to a set of recursive predicates given their ids") {
    val predId = "rec"
    val maybeRecursiveBody = Some(PredicateAccessPredicate(PredicateAccess(Seq(), predId)(), FullPerm.apply()())())
    val recursivePred = Predicate(predId, formalArgs = Seq(), body = maybeRecursiveBody)()
    val program = programCopy(predicates = Seq(recursivePred))

    val result = findLoopBreakers(predicateIds = Set(predId), program)
    assert(result.size == 1 && result.forall(name => name == predId))
  }

  test("findLoopBreakers should evaluate to a set of recursive predicates given a deeper body") {
    val predId = "rec"
    val recursivePredAcc = PredicateAccessPredicate(PredicateAccess(Seq(), predId)(), FullPerm.apply()())()
    val maybeRecursiveBody = Some(And(IntLit(11)(), recursivePredAcc)())
    val recursivePred = Predicate(predId, formalArgs = Seq(), body = maybeRecursiveBody)()
    val program = programCopy(predicates = Seq(recursivePred))

    val result = findLoopBreakers(predicateIds = Set(predId), program)
    assert(result.size == 1 && result(recursivePred.name))
  }

  test("findLoopBreakers should evaluate to a set of recursive predicates given a number of recursive preds") {
    val firstRec = "firstRec"
    val secondRec = "secondRec"
    val firstRecursivePredAcc = PredicateAccessPredicate(PredicateAccess(Seq(), firstRec)(), FullPerm.apply()())()
    val secondRecursivePredAcc = PredicateAccessPredicate(PredicateAccess(Seq(), secondRec)(), FullPerm.apply()())()
    val maybeFirstRecursiveBody = Some(And(IntLit(11)(), firstRecursivePredAcc)())
    val maybeSecondRecursiveBody = Some(And(IntLit(11)(), And(IntLit(44)(), secondRecursivePredAcc)())())
    val firstRecursivePred = Predicate(firstRec, formalArgs = Seq(), body = maybeFirstRecursiveBody)()
    val secondRecursivePred = Predicate(secondRec, formalArgs = Seq(), body = maybeSecondRecursiveBody)()
    val program = programCopy(predicates = Seq(firstRecursivePred, secondRecursivePred))

    val result = findLoopBreakers(predicateIds = Set(firstRec, secondRec), program)
    assert(result.size == 2 && result(firstRecursivePred.name) && result(secondRecursivePred.name))
  }

  test("findLoopBreakers should evaluate to an empty set given the id of a non-recursive predicate") {
    val predId = "nonrec"
    val maybeNonRecursiveBody = Some(Add(IntLit(69)(), IntLit(420)())())
    val nonRecursivePred = Predicate(predId, formalArgs = Seq(), body = maybeNonRecursiveBody)()
    val program = programCopy(predicates = Seq(nonRecursivePred))

    assert(findLoopBreakers(predicateIds = Set(predId), program).isEmpty)
  }

  test("findLoopBreakers should evaluate to an empty set given a program with only non-recursive predicates") {
    val addPredId = "blazeIt"
    val maybeNonRecursiveBody = Some(Add(IntLit(69)(), IntLit(420)())())
    val addPred = Predicate(addPredId, formalArgs = Seq(), body = maybeNonRecursiveBody)()
    val emptyPredId = "noBody"
    val emptyPred = Predicate(emptyPredId, formalArgs = Seq(), body = None)()
    val program = programCopy(predicates = Seq(addPred, emptyPred))

    assert(findLoopBreakers(predicateIds = Set(addPredId, emptyPredId), program).isEmpty)
  }

  test("findLoopBreakers should evaluate to a set containing mutually-recursive predicates given their ids") {
    val firstPredId = "list"
    val secondPredId = "calledByList"
    val maybeFirstPredBody = Some(PredicateAccessPredicate(PredicateAccess(Seq(), secondPredId)(), FullPerm.apply()())())
    val maybeSecondPredBody = Some(PredicateAccessPredicate(PredicateAccess(Seq(), firstPredId)(), FullPerm.apply()())())
    val firstPred = Predicate(firstPredId, formalArgs = Seq(), body = maybeFirstPredBody)()
    val secondPred = Predicate(secondPredId, formalArgs = Seq(), body = maybeSecondPredBody)()
    val program = programCopy(predicates = Seq(firstPred, secondPred))

    val result = findLoopBreakers(Set(firstPredId, secondPredId), program)
    assert(result.size == 1 && result.forall(Set(firstPredId, secondPredId)(_)))
  }

}
