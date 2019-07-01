// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.trafo.util

import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast._
import viper.silver.verifier.ConsistencyError
import viper.silver.plugin.{DecreasesExp, DecreasesStar, DecreasesTuple}

import scala.collection.immutable.ListMap

/**
  * A basic interface to help create termination checks.
  *
  * Therefore it needs following things in the program:
  * "decreasing" domain function
  * "bounded" domain function
  */
trait DecreasesCheck extends ProgramManager with PredicateInstanceManager {

  protected val decreasingFunc: Option[DomainFunc] = program.findDomainFunctionOptionally("decreasing")
  protected val boundedFunc: Option[DomainFunc] =  program.findDomainFunctionOptionally("bounded")

  /**
    * Creates a termination check.
    * If decreasing and bounded functions are not defined a consistency error is reported.
    * @param biggerDec DecreaseExp of the function currently checked
    * @param smallerDec DecreaseExp of the function called
    * @param argMap Substitutions for smallerDec
    * @param errTrafo for termination related assertions
    * @param reasonTrafoFactory for termination related assertion reasons
    * @param context of the current termination check
    * @return termination check as a Assert Stmt (if decreasing and bounded are defined, otherwise EmptyStmt)
    */
  def createTerminationCheck(biggerDec: DecreasesExp, smallerDec: DecreasesExp, argMap: Map[LocalVar, Node],
                             errTrafo: ErrTrafo, reasonTrafoFactory: ReasonTrafoFactory, context: ProofMethodContext): Stmt = {
    (biggerDec, smallerDec) match {
      case (dt: DecreasesTuple, ds: DecreasesStar) =>
        val reTStar = reasonTrafoFactory.createStar(context)
        Assert(FalseLit()(errT = reTStar))(errT = errTrafo)
      case (dtBig: DecreasesTuple, dtSmall: DecreasesTuple) =>
        val biggerExp: Seq[Exp] = dtBig.subExps
        val smallerExp: Seq[Exp] = dtSmall.subExps

        // decreasing and bounded functions are needed
        if(decreasingFunc.isDefined && boundedFunc.isDefined) {
          // trims to the longest commonly typed prefix
          val (bExp, sExp) = (biggerExp zip smallerExp.map(_.replace(argMap))).takeWhile(exps => exps._1.typ == exps._2.typ).unzip

          val reTBound = reasonTrafoFactory.createNotBounded(bExp, context)

          val reTDec = reasonTrafoFactory.createNotDecrease(bExp, sExp, context)

          val checkableBiggerExp = bExp.map({
            case pa: PredicateAccessPredicate =>
              if (PredicateInstanceDomain.isDefined) {
                // use the init predicate variable
                val varOfCalleePred = getInitPredicateInstanceVar(context.methodName, pa)
                varOfCalleePred.localVar
              } else {
                reportPredicateInstanceNotDefined(biggerDec.pos)
                pa
              }
            case default => default
          })

          var newVarPred = scala.collection.mutable.Map[PredicateAccessPredicate, LocalVarDecl]()

          val checkableSmallerExp = sExp.map({
            case pa: PredicateAccessPredicate =>
              if (PredicateInstanceDomain.isDefined) {
                val varOfCalleePred = uniquePredicateInstanceVar(pa.loc)
                newVarPred(pa) = varOfCalleePred
                varOfCalleePred.localVar
              } else {
                reportPredicateInstanceNotDefined(biggerDec.pos)
                pa
              }
            case default => default
          })

          val newVarPredAss: Seq[Stmt] = newVarPred.map(v => generatePredicateAssign(v._2.localVar, v._1.loc)).toSeq

          val check = createTerminationCheckExp(checkableBiggerExp, checkableSmallerExp, reTDec, reTBound)
          val assert = Assert(check)(errT = errTrafo)

          Seqn(newVarPredAss :+ assert, newVarPred.values.toSeq)()
        }else{
          // at least of the needed functions is not defined
          if (decreasingFunc.isEmpty){
            reportDecreasingNotDefined(biggerDec.pos)
          }
          if (boundedFunc.isEmpty){
            reportBoundedNotDefined(biggerDec.pos)
          }
          EmptyStmt
        }
      case _ =>
        assert(assertion = false, "Checking termination of a member declared with DecreasesStar! " +
          "This should not happen!")
        Assert(FalseLit()())(errT = errTrafo)
    }
  }

  /**
    * If expressions are not empty
    * creates Expression to check decrease and bounded in lexicographical order.
    * The bigger expressions are all enclosed in old() expressions!
    * (decreasing(s,b) && bounded(b)) || (s==b && ( (decr...
    * decreasingFunc and boundedFunc have to be defined!
    * @param biggerExp [b,..] (can also be empty)
    * @param smallerExp [s,..] same size as biggerExp!
    * @return expression or false if expression is empty
    */
  private def createTerminationCheckExp(biggerExp: Seq[Exp], smallerExp: Seq[Exp], decrReTrafo: ReTrafo, boundReTrafo: ReTrafo): Exp = {
    assert(biggerExp.size == smallerExp.size)
    assert(decreasingFunc.isDefined)
    assert(boundedFunc.isDefined)

    if (biggerExp.isEmpty){
      FalseLit()(errT = decrReTrafo)
    }else {
      val paramTypesDecr = decreasingFunc.get.formalArgs map (_.typ)
      val argTypeVarsDecr = paramTypesDecr.flatMap(p => p.typeVariables)
      val paramTypesBound = boundedFunc.get.formalArgs map (_.typ)
      val argTypeVarsBound = paramTypesBound.flatMap(p => p.typeVariables)

      /**
        * Recursive function to create the check expression
        */
      def createExp(biggerExp: Seq[Exp], smallerExp: Seq[Exp]): Exp = {
        assert(biggerExp.nonEmpty)
        assert(biggerExp.size == smallerExp.size)
        val bigger = biggerExp.head
        val biggerOld = Old(biggerExp.head)(bigger.pos, bigger.info, bigger.errT)
        val smaller = smallerExp.head
        val dec = DomainFuncApp(decreasingFunc.get,
          Seq(smaller, biggerOld),
          ListMap(argTypeVarsDecr.head -> smaller.typ,
            argTypeVarsDecr.last -> bigger.typ))(errT = decrReTrafo)

        val bound = DomainFuncApp(boundedFunc.get,
          Seq(biggerOld),
          ListMap(argTypeVarsDecr.head -> bigger.typ,
            argTypeVarsDecr.last -> bigger.typ
          ))(errT = boundReTrafo)

        val andPart = And(dec, bound)()

        if (biggerExp.size == 1) {
          // no next elements
          andPart
        } else {
          val eq = EqCmp(smaller, bigger)(errT = decrReTrafo)
          val next = createExp(biggerExp.tail, smallerExp.tail)
          val nextPart = And(eq, next)()
          Or(andPart, nextPart)()
        }
      }

      createExp(biggerExp, smallerExp)
    }
  }

  def reportDecreasingNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("Decreasing function is needed but not defined.", pos))
  }

  def reportBoundedNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("Bounded function is needed but not defined.", pos))
  }
}
