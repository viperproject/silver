package plugin.inline

import org.scalatest.FunSuite
import viper.silver.ast._
import viper.silver.plugin.standard.inline.InlineErrorChecker

class InlineErrorCheckerTest extends FunSuite with InlineErrorChecker with InlineTestFixture {

  test("checkRecursive should evaluate to an empty set given an empty set of predicates") {
    val program = programCopy()

    assert(checkRecursive(predicateIds = Set(), program).isEmpty)
  }

  test("checkRecursive should evaluate to an empty set given a non-recursive predicate") {
    val predId = "nonrec"
    val maybeNonRecursiveBody = Some(Add(IntLit(69)(), IntLit(420)())())
    val nonRecursivePred = Predicate(predId, formalArgs = Seq(), body = maybeNonRecursiveBody)()
    val program = programCopy(predicates = Seq(nonRecursivePred))

    assert(checkRecursive(predicateIds = Set(predId), program).isEmpty)
  }

  test("checkRecursive should evaluate to a set of recursive predicates given their ids") {
    val predId = "rec"
    val maybeRecursiveBody = Some(PredicateAccessPredicate(PredicateAccess(Seq(), predId)(), FullPerm.apply()())())
    val recursivePred = Predicate(predId, formalArgs = Seq(), body = maybeRecursiveBody)()
    val program = programCopy(predicates = Seq(recursivePred))

    val result = checkRecursive(predicateIds = Set(predId), program)
    assert(result.size == 1 && result.forall {
      case Predicate(name, _, _) => name == predId
      case _ => false
    })
  }

  test("checkRecursive should evaluate to a set of recursive predicates given a deeper body") {
    val predId = "rec"
    val recursivePredAcc = PredicateAccessPredicate(PredicateAccess(Seq(), predId)(), FullPerm.apply()())()
    val maybeRecursiveBody = Some(And(IntLit(11)(), recursivePredAcc)())
    val recursivePred = Predicate(predId, formalArgs = Seq(), body = maybeRecursiveBody)()
    val program = programCopy(predicates = Seq(recursivePred))

    val result = checkRecursive(predicateIds = Set(predId), program)
    assert(result.size == 1 && result(recursivePred))
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
    assert(result.size == 2 && result(firstRecursivePred) && result(secondRecursivePred))
  }

  test("checkMutualRecursive should evaluate to an empty set given an empty set of predicates") {
    val program = programCopy()

   assert(checkMutualRecursive(predicateIds = Set(), program).isEmpty)
  }

  test("checkMutualRecursive should evaluate to an empty set given the id of a non-recursive predicate") {
    val predId = "nonrec"
    val maybeNonRecursiveBody = Some(Add(IntLit(69)(), IntLit(420)())())
    val nonRecursivePred = Predicate(predId, formalArgs = Seq(), body = maybeNonRecursiveBody)()
    val program = programCopy(predicates = Seq(nonRecursivePred))

    assert(checkMutualRecursive(predicateIds = Set(predId), program).isEmpty)
  }

  test("checkMutualRecursive should evaluate to an empty set given a program with only non-recursive predicates") {
    val addPredId = "blazeIt"
    val maybeNonRecursiveBody = Some(Add(IntLit(69)(), IntLit(420)())())
    val addPred = Predicate(addPredId, formalArgs = Seq(), body = maybeNonRecursiveBody)()
    val emptyPredId = "noBody"
    val emptyPred = Predicate(emptyPredId, formalArgs = Seq(), body = None)()
    val program = programCopy(predicates = Seq(addPred, emptyPred))

    assert(checkMutualRecursive(predicateIds = Set(addPredId, emptyPredId), program).isEmpty)
  }

  test("checkMutualRecursive should evaluate to a set containing mutually-recursive predicates given their ids") {
    val firstPredId = "list"
    val secondPredId = "calledByList"
    val maybeFirstPredBody = Some(PredicateAccessPredicate(PredicateAccess(Seq(), secondPredId)(), FullPerm.apply()())())
    val maybeSecondPredBody = Some(PredicateAccessPredicate(PredicateAccess(Seq(), firstPredId)(), FullPerm.apply()())())
    val firstPred = Predicate(firstPredId, formalArgs = Seq(), body = maybeFirstPredBody)()
    val secondPred = Predicate(secondPredId, formalArgs = Seq(), body = maybeSecondPredBody)()
    val program = programCopy(predicates = Seq(firstPred, secondPred))

    val result = checkMutualRecursive(Set(firstPredId, secondPredId), program)
    assert(result.size == 2 && result(firstPred) && result(secondPred))
  }

  test("predicatesCalledBy should evaluate to None given a predicate with an empty body") {
    val emptyPred = Predicate("empty", Seq(), body = None)()
    val program = programCopy()

    assert(nonRecursivePredsCalledBy(emptyPred, Set(), program).isEmpty)
  }

  test("predicatesCalledBy should not return predicates names for recursive preds") {
    val predId = "rec"
    val maybeRecursiveBody = Some(PredicateAccessPredicate(PredicateAccess(Seq(), predId)(), FullPerm.apply()())())
    val recursivePred = Predicate(predId, formalArgs = Seq(), body = maybeRecursiveBody)()
    val program = programCopy()

    assert(nonRecursivePredsCalledBy(recursivePred, Set("rec"), program).isEmpty)
  }

  test("predicatesCalledBy should return predicates called in the body of the given predicate") {
    val calledPredId = "F"
    val recursivePredId = "loop"
    val maybeRecursiveBody = Some(
      And(
        PredicateAccessPredicate(PredicateAccess(Seq(), recursivePredId)(), FullPerm.apply()())(),
        PredicateAccessPredicate(PredicateAccess(Seq(), calledPredId)(), FullPerm.apply()())(),
      )()
    )
    val predicateForF = Predicate(calledPredId, Seq(), None)()
    val program = programCopy(predicates = Seq(predicateForF))
    val pred = Predicate("loop", formalArgs = Seq(), body = maybeRecursiveBody)()

    val result = nonRecursivePredsCalledBy(pred, Set("loop"), program)
    assert(result.size == 1 && result(calledPredId))
  }

  test("predicatesCalledBy should traverse subpredicates") {
    /*
    predicate F(this: Ref) {
      G(this)
    }

    predicate G(this: Ref) {
      acc(x.f)
    }

    predicate loop(this: Ref) {
      loop(this) && F(this)
    }
     */
    val f = "F"
    val g = "G"
    val loop = "loop"
    val fBody = Some(PredicateAccessPredicate(PredicateAccess(Seq(), g)(), FullPerm.apply()())())
    val gBody = Some(FieldAccessPredicate(FieldAccess(LocalVar("x", Ref)(),Field("left", Int)(NoPosition))(), FullPerm.apply()())())
    val loopBody = Some(
      And(
        PredicateAccessPredicate(PredicateAccess(Seq(), f)(), FullPerm.apply()())(),
        PredicateAccessPredicate(PredicateAccess(Seq(), loop)(), FullPerm.apply()())(),
      )()
    )
    val loopPred = Predicate("loop", formalArgs = Seq(), body = loopBody)()
    val program = programCopy(
      predicates = Seq(
        loopPred,
        Predicate(f, formalArgs = Seq(), body = fBody)(),
        Predicate(g, formalArgs = Seq(), body = gBody)(),
      )
    )

    val result = nonRecursivePredsCalledBy(loopPred, Set("loop"), program)
    assert(result.size == 2 && Set(f, g) == result)
  }
}
