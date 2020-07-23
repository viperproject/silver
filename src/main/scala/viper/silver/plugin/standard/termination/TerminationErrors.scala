// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination

import viper.silver.verifier.reasons.ErrorNode
import viper.silver.verifier._

/*
  All Errors and Reasons concerning termination checks
  and factories for such reasons.
 */

/**
 * Error for all termination related failed assertions.
 */
abstract class AbstractTerminationError() extends AbstractVerificationError {
  override val id = "termination.failed"
}

case class FunctionTerminationError(override val offendingNode: ErrorNode,
                                    override val reason: ErrorReason,
                                    override val cached: Boolean = false) extends AbstractTerminationError {
  override val text = s"Function might not terminate."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode): FunctionTerminationError =
    FunctionTerminationError(this.offendingNode, this.reason)

  override def withReason(r: ErrorReason): FunctionTerminationError = FunctionTerminationError(offendingNode, r)
}

case class MethodTerminationError(override val offendingNode: ErrorNode,
                                  override val reason: ErrorReason,
                                  override val cached: Boolean = false) extends AbstractTerminationError {
  override val text = s"Method might not terminate."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode): MethodTerminationError =
    MethodTerminationError(this.offendingNode, this.reason)

  override def withReason(r: ErrorReason): MethodTerminationError = MethodTerminationError(offendingNode, r)
}

case class LoopTerminationError(override val offendingNode: ErrorNode,
                                override val reason: ErrorReason,
                                override val cached: Boolean = false) extends AbstractTerminationError {
  override val text = s"Loop might not terminate."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode): LoopTerminationError =
    LoopTerminationError(this.offendingNode, this.reason)

  override def withReason(r: ErrorReason): LoopTerminationError = LoopTerminationError(offendingNode, r)
}


/*
 Reasons for all termination related failed assertions.
 */

case class TerminationConditionFalse(offendingNode: ErrorNode) extends AbstractErrorReason {
  override val id: String = "termination.condition.false"

  override val readableMessage: String = s"Required termination condition might not hold."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TerminationConditionFalse(offendingNode)
}

case class TupleConditionFalse(offendingNode: ErrorNode) extends AbstractErrorReason {
  override val id: String = "tuple.condition.false"

  override val readableMessage: String = s"Required tuple condition might not hold."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TupleConditionFalse(offendingNode)
}

case class TupleSimpleFalse(offendingNode: ErrorNode) extends AbstractErrorReason {
  override val id: String = "tuple.false"

  override val readableMessage: String = s"Termination measure might not decrease or might not be bounded."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TupleSimpleFalse(offendingNode)
}

case class TupleDecreasesFalse(offendingNode: ErrorNode) extends AbstractErrorReason {
  override val id: String = "tuple.false"

  override val readableMessage: String = s"Termination measure might not decrease."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TupleDecreasesFalse(offendingNode)
}

case class TupleBoundedFalse(offendingNode: ErrorNode) extends AbstractErrorReason {
  override val id: String = "tuple.false"

  override val readableMessage: String = s"Termination measure might not bounded."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TupleBoundedFalse(offendingNode)
}