package plugin.inline

import org.scalatest.FunSuite
import viper.silver.ast.{Add, And, FullPerm, IntLit, Predicate, PredicateAccess, PredicateAccessPredicate}
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

  test("checkRecursive should evaluate to a set of recursive predicates given a deeper body") {
    val predId = "rec"
    val recursivePredAcc = PredicateAccessPredicate(PredicateAccess(Seq(), predId)(), FullPerm.apply()())()
    val maybeRecursiveBody = Some(And(IntLit(11)(), recursivePredAcc)())
    val recursivePred = Predicate(predId, formalArgs = Seq(), body = maybeRecursiveBody)()
    val program = programCopy(predicates = Seq(recursivePred))

    val result = checkRecursive(predicateIds = Set(predId), program)
    result.size == 1 && result(recursivePred)
  }

  test("checkRecursive should evaluate to a set of recursive predicates given a number of recursive preds") {
    val firstRec = "firstRec"
    val secondRec = "secondRec"
    val firstRecursivePredAcc = PredicateAccessPredicate(PredicateAccess(Seq(), firstRec)(), FullPerm.apply()())()
    val secondRecursivePredAcc = PredicateAccessPredicate(PredicateAccess(Seq(), secondRec)(), FullPerm.apply()())()
    val maybeFirstRecursiveBody = Some(And(IntLit(11)(), firstRecursivePredAcc)())
    val maybeSecondRecursiveBody = Some(And(IntLit(11)(), And(IntLit(44)(), secondRecursivePredAcc)())())
    val firstRecursivePred = Predicate(firstRec, formalArgs = Seq(), body = maybeFirstRecursiveBody)()
    val secondRecursivePred = Predicate(secondRec, formalArgs = Seq(), body = maybeSecondRecursiveBody)()
    val program = programCopy(predicates = Seq(firstRecursivePred, secondRecursivePred))

    val result = checkRecursive(predicateIds = Set(firstRec, secondRec), program)
    result.size == 2 && result(firstRecursivePred) && result(secondRecursivePred)
  }
}
