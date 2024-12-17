package viper.silver.plugin.standard.loopspecs



import viper.silver.verifier.reasons.ErrorNode
import viper.silver.verifier._


//no need to subclass reasons, only make new errors (overwrite id and text for user)

/*
  All Errors and Reasons concerning termination checks
  and factories for such reasons.
 */

/**
 * Error for all termination related failed assertions.
 */
sealed abstract class AbstractTerminationError extends ExtensionAbstractVerificationError {
  override val id = "termination.failed"
}

sealed abstract class TerminationErrorReason extends ExtensionAbstractErrorReason

case class FunctionTerminationError(override val offendingNode: ErrorNode,
                                    override val reason: ErrorReason,
                                    override val cached: Boolean = false) extends AbstractTerminationError {
  override val text = s"Function might not terminate."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode): FunctionTerminationError =
    FunctionTerminationError(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason): FunctionTerminationError = FunctionTerminationError(offendingNode, r, cached)
}

case class MethodTerminationError(override val offendingNode: ErrorNode,
                                  override val reason: ErrorReason,
                                  override val cached: Boolean = false) extends AbstractTerminationError {
  override val text = s"Method might not terminate."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode): MethodTerminationError =
    MethodTerminationError(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason): MethodTerminationError = MethodTerminationError(offendingNode, r, this.cached)
}

case class LoopTerminationError(override val offendingNode: ErrorNode,
                                override val reason: ErrorReason,
                                override val cached: Boolean = false) extends AbstractTerminationError {
  override val text = s"Loop might not terminate."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode): LoopTerminationError =
    LoopTerminationError(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason): LoopTerminationError = LoopTerminationError(offendingNode, r, cached)
}


/*
 Reasons for all termination related failed assertions.
 */

case class TerminationConditionFalse(offendingNode: ErrorNode) extends TerminationErrorReason {
  override val id: String = "termination.condition.false"

  override val readableMessage: String = s"Required termination condition might not hold."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TerminationConditionFalse(offendingNode)
}

case class TupleConditionFalse(offendingNode: ErrorNode) extends TerminationErrorReason {
  override val id: String = "tuple.condition.false"

  override val readableMessage: String = s"Required tuple condition might not hold."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TupleConditionFalse(offendingNode)
}

case class TupleSimpleFalse(offendingNode: ErrorNode) extends TerminationErrorReason {
  override val id: String = "tuple.false"

  override val readableMessage: String = s"Termination measure might not decrease or might not be bounded."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TupleSimpleFalse(offendingNode)
}

case class TupleDecreasesFalse(offendingNode: ErrorNode) extends TerminationErrorReason {
  override val id: String = "tuple.false"

  override val readableMessage: String = s"Termination measure might not decrease."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TupleDecreasesFalse(offendingNode)
}

case class TupleBoundedFalse(offendingNode: ErrorNode) extends TerminationErrorReason {
  override val id: String = "tuple.false"

  override val readableMessage: String = s"Termination measure might not bounded."

  override def withNode(offendingNode: ErrorNode): ErrorMessage = TupleBoundedFalse(offendingNode)
}
