// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.trafo.util

import viper.silver.ast._
import viper.silver.verifier.reasons.{AssertionFalse, ErrorNode}
import viper.silver.verifier.{AbstractErrorReason, AbstractVerificationError, ErrorReason, errors}
import viper.silver.plugin.{DecreasesExp, DecreasesTuple}

/*
  All Errors and Reasons concerning termination checks and the Reason Factories.
 */

/**
  * Error for all termination related failed assertions.
  */
abstract class AbstractTerminationError() extends AbstractVerificationError {
  val id = "termination.failed"
}

case class FunctionTerminationError(override val offendingNode: ErrorNode, override val reason: ErrorReason, override val cached: Boolean = false) extends AbstractTerminationError {
  val text = s"Function might not terminate."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = FunctionTerminationError(this.offendingNode, this.reason)
  def withReason(r: ErrorReason) = FunctionTerminationError(offendingNode, r)
}

case class MethodTerminationError(override val offendingNode: ErrorNode, override val reason: ErrorReason, override val cached: Boolean = false) extends AbstractTerminationError {
  val text = s"Method might not terminate."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = MethodTerminationError(this.offendingNode, this.reason)
  def withReason(r: ErrorReason) = MethodTerminationError(offendingNode, r)
}


/**
  * Interface for factories creating trafos of non-termination reasons.
  */
trait ReasonTrafoFactory{
  def createNotDecrease(biggerDec: Seq[Exp], smallerDec: Seq[Exp], context: Context): ReTrafo
  def createNotBounded(biggerDec: Seq[Exp], context: Context): ReTrafo
  def createStar(context: Context): ReTrafo
}


//### SIMPLE REASONS ###
case class SimpleReasonTrafoFactory(offendingNode: DecreasesTuple) extends ReasonTrafoFactory {
  override def createNotDecrease(biggerDec: Seq[Exp], smallerDec: Seq[Exp], context: Context): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TerminationNoDecrease(offendingNode, biggerDec, smallerDec) })
  }

  override def createNotBounded(biggerDec: Seq[Exp], context: Context): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TerminationNoBound(offendingNode, biggerDec) })
  }

  override def createStar(context: Context): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TerminationStar(offendingNode) })
  }
}

//### NON-TERMINATION REASONS ###
case class TerminationNoDecrease(offendingNode: DecreasesTuple, decOrigin: Seq[Exp], decDest: Seq[Exp]) extends AbstractErrorReason {
  val id = "termination.no.decrease"
  override def readableMessage: String = s"Termination measure might not decrease. " +
    s"Assertion (${decDest.mkString(", ")})≺(${decOrigin.mkString(", ")}) might not hold."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoDecrease(this.offendingNode, decOrigin, decDest)
}

case class TerminationNoBound(offendingNode: DecreasesTuple, decExp: Seq[Exp]) extends AbstractErrorReason {
  val id = "termination.no.bound"
  override def readableMessage: String = s"Termination measure might not be bounded. " +
    s"Assertion 0≺(${decExp.mkString(", ")}) might not hold."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoBound(this.offendingNode, decExp)
}

case class TerminationStar(offendingNode: DecreasesTuple) extends AbstractErrorReason {
  val id = "termination.star"
  override def readableMessage = s"Cannot prove termination, if member declared with decreasesStar is called."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationStar(this.offendingNode)
}


//### PATH NON-TERMINATION REASONS ###
case class PathReasonTrafoFactory(offendingNode: DecreasesTuple, offendingPath: Seq[FuncApp]) extends ReasonTrafoFactory {
  override def createNotDecrease(biggerDec: Seq[Exp], smallerDec: Seq[Exp], context: Context): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TerminationNoDecreasePath(offendingNode, biggerDec, smallerDec, offendingPath) })
  }

  override def createNotBounded(biggerDec: Seq[Exp], context: Context): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TerminationNoBoundPath(offendingNode, biggerDec, offendingPath) })
  }

  override def createStar(context: Context): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TerminationStarPath(offendingNode, offendingPath) })
  }
}

case class TerminationNoDecreasePath(offendingNode: DecreasesExp, decOrigin: Seq[Exp], decDest: Seq[Exp], offendingPath: Seq[FuncApp]) extends AbstractErrorReason {
  val id = "termination.no.decrease"
  override def readableMessage: String = s"Termination measure might not decrease. " +
    s"Assertion (${decDest.mkString(", ")})≺(${decOrigin.mkString(", ")}) might not hold. " +
    s"\nPath: ${PathReasonPrinter.getReadablePath(offendingPath)}."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoDecreasePath(this.offendingNode, decOrigin, decDest, offendingPath)
}

case class TerminationNoBoundPath(offendingNode: DecreasesExp, decExp: Seq[Exp], offendingPath: Seq[FuncApp]) extends AbstractErrorReason {
  val id = "termination.no.bound"
  override def readableMessage: String = s"Termination measure might not be bounded. " +
    s"Assertion 0≺(${decExp.mkString(", ")}) might not hold. " +
    s"\nPath: ${PathReasonPrinter.getReadablePath(offendingPath)}."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoBoundPath(this.offendingNode, decExp, offendingPath)
}

case class TerminationStarPath(offendingNode: DecreasesExp, offendingPath: Seq[FuncApp]) extends AbstractErrorReason {
  val id = "termination.star"
  override def readableMessage: String = s"Cannot prove termination, if member declared with decreasesStar is called." +
    s"\nPath: ${PathReasonPrinter.getReadablePath(offendingPath)}."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationStarPath(this.offendingNode, offendingPath)
}

/**
  * Utility object to create readable path from sequnce of function applications.
  */
object PathReasonPrinter{
  def getReadablePath(path: Seq[FuncApp]): String = {
    path.map(f => s"$f@${
      f.pos match {
        case NoPosition =>"noPos"
        case p: HasLineColumn => s"${p.line}.${p.column}"
      }}").mkString(" -> ")
  }
}