// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import viper.silver.ast._
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.verifier.ConsistencyError

import scala.collection.immutable.ListMap

/**
 * A basic interface to help create termination checks.
 *
 * The following features have to be defined in the program (program field of ProgramManager)
 * otherwise a consistency error is issued.
 * "decreasing" domain function
 * "bounded" domain function
 */
trait DecreasesCheck extends ProgramManager with ErrorReporter {

  protected val decreasingFunc: Option[DomainFunc] = program.findDomainFunctionOptionally("decreasing")
  protected val boundedFunc: Option[DomainFunc] = program.findDomainFunctionOptionally("bounded")


  /**
   * Creates a check to determine if requiredCondition implies givenCondition.
   *
   * @param errTrafo to be used for the Assertion (default: true)
   * @param reTrafo  to be used in the Assertion (default: true)
   * @return a Stmt containing the check
   */
  protected def createConditionCheck(requiredCondition: Option[Exp], givenCondition: Option[Exp],
                                     errTrafo: ErrTrafo, reTrafo: ReTrafo): Stmt = {

    // When Implies is used, error reason would point to right side of implication (i.e. givenCondition),
    // for which no reason transformation can be defined. (this happens in carbon)
    // To avoid this and equivalent expression using Or is used.

    val rCondition = requiredCondition.getOrElse(TrueLit()(errT = reTrafo))
    val gCondition = givenCondition.getOrElse(TrueLit()(errT = reTrafo))

    val or = Or(Not(rCondition)(errT = reTrafo), gCondition)(errT = reTrafo)

    Assert(or)(errT = errTrafo)
  }


  /**
   * Creates checks to determine if the tuple decreases,
   * under the tuple condition of the bigger tuple.
   * If decreasing and bounded functions are not defined a consistency error is reported.
   *
   * @param tupleCondition     for which tuple decreasing should be checked (default: true)
   * @param errTrafo           for termination related assertions
   * @param reasonTrafoFactory for termination related assertion reasons
   * @return termination check as a Assert Stmt (if decreasing and bounded are defined, otherwise EmptyStmt)
   */
  protected def createTupleCheck(tupleCondition: Option[Exp], biggerTuple: Seq[Exp], smallerTuple: Seq[Exp],
                                 errTrafo: ErrTrafo, reasonTrafoFactory: ReasonTrafoFactory): Stmt = {

    if (decreasingFunc.isEmpty || boundedFunc.isEmpty) {
      if (decreasingFunc.isEmpty) {
        reportDecreasingNotDefined(reasonTrafoFactory.offendingNode.pos)
      }
      if (boundedFunc.isEmpty) {
        reportBoundedNotDefined(reasonTrafoFactory.offendingNode.pos)
      }
      return EmptyStmt
    }

    //val dtSmall = smallerTuple.tupleExpressions.map(_.replace(argMap))

    val lexCheck = createLexDecreaseCheck(biggerTuple, smallerTuple, reasonTrafoFactory)

    val decreasesSimpleReasonTrafo = reasonTrafoFactory.generateTupleSimpleFalse()

    val tupleImplies = tupleCondition match {
      case Some(c) => Implies(c, lexCheck)(errT = decreasesSimpleReasonTrafo)
      case None => lexCheck
    }

    val tupleAssert = Assert(tupleImplies)(errT = errTrafo)

    tupleAssert
  }

  /**
   * Creates Expression checking decreasing and boundedness of the two tuples in lexicographical order.
   * (decreasing(s[0],b[0]) && bounded(b[0])) || (s[0]==b[0] && ( createLexDecreaseCheck(s{1..], b[1..]))
   * Further, both tuples are considered to be extended with a TOP object,
   * which is considered bigger than any other object.
   * If the smallerTuple is empty, false is returned.
   * decreasingFunc and boundedFunc must be defined.
   *
   * @param biggerTuple  tuple do be considered bigger
   * @param smallerTuple tuple do be considered smaller
   * @return expression or false if smaller expression is empty
   */
  private def createLexDecreaseCheck(biggerTuple: Seq[Exp], smallerTuple: Seq[Exp], reasonTrafoFactory: ReasonTrafoFactory): Exp = {

    assert(decreasingFunc.isDefined)
    assert(boundedFunc.isDefined)

    val simpleReTrafo = reasonTrafoFactory.generateTupleSimpleFalse()
    val decreasesReTrafo = reasonTrafoFactory.generateTupleDecreasesFalse()
    val boundReTrafo = reasonTrafoFactory.generateTupleBoundedFalse()


    val paramTypesDecr = decreasingFunc.get.formalArgs map (_.typ)
    val argTypeVarsDecr = paramTypesDecr.flatMap(p => p.typeVariables)
    val paramTypesBound = boundedFunc.get.formalArgs map (_.typ)
    val argTypeVarsBound = paramTypesBound.flatMap(p => p.typeVariables)

    /**
     * Recursive function to create the check expression
     */
    def createExp(bTuple: Seq[Exp], sTuple: Seq[Exp]): Exp = {
      if (sTuple.isEmpty) {
        // smaller tuple would now be appended with TOP
        // TOP cannot be smaller than any expression in the bigger tuple
        FalseLit()(errT = decreasesReTrafo)
      } else if (bTuple.isEmpty) {
        // smaller tuple still has an element
        // bigger tuple would now be appended with TOP
        // any element (besides TOP) is smaller than TOP
        TrueLit()(errT = simpleReTrafo)
      } else {
        // both tuples still have at least one element
        val bigger = bTuple.head
        val smaller = sTuple.head

        if (!(bigger.isSubtype(smaller) || smaller.isSubtype(bigger))) {
          // not same types
          FalseLit()(errT = decreasesReTrafo)
        } else {
          // same type

          val dec = DomainFuncApp(decreasingFunc.get,
            Seq(smaller, bigger),
            Map(argTypeVarsDecr.head -> smaller.typ,
              argTypeVarsDecr.last -> bigger.typ))(errT = decreasesReTrafo)

          val bound = DomainFuncApp(boundedFunc.get,
            Seq(bigger),
            ListMap(argTypeVarsBound.head -> bigger.typ,
              argTypeVarsDecr.last -> bigger.typ
            ))(errT = boundReTrafo)

          val andPart = And(dec, bound)(errT = simpleReTrafo)

          val eq = EqCmp(smaller, bigger)(errT = decreasesReTrafo)

          val next = createExp(bTuple.tail, sTuple.tail)
          val nextPart = And(eq, next)(errT = simpleReTrafo)
          Or(andPart, nextPart)(errT = simpleReTrafo)
        }
      }
    }

    createExp(biggerTuple, smallerTuple)
  }

  def reportDecreasingNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("Function \"decreasing\" is required but not declared.", pos))
  }

  def reportBoundedNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("Function \"bounded\" is required but not defined.", pos))
  }
}