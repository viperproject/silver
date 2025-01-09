package viper.silver.plugin.standard.loopspecs



import viper.silver.verifier.reasons.ErrorNode
import viper.silver.verifier._


//no need to subclass reasons, only make new errors (overwrite id and text for user)

/*
  All Errors and Reasons concerning termination checks
  and factories for such reasons.
 */


case class PreconditionNotEstablished(override val offendingNode: ErrorNode,
                                    override val reason: ErrorReason,
                                    override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"precondition.not.established"
  override val text = s"Precondition $offendingNode might not hold on entry."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PreconditionNotEstablished(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PreconditionNotEstablished(offendingNode, r, cached)
}

case class PreconditionNotPreserved(override val offendingNode: ErrorNode,
                                      override val reason: ErrorReason,
                                      override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"precondition.not.preserved"
  override val text = s"Precondition $offendingNode might not be preserved."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PreconditionNotPreserved(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PreconditionNotPreserved(offendingNode, r, cached)
}

//TODO: Postcondition exhale i == 1 ==> Postcondition  i == 1
case class PostconditionNotPreservedBaseCase(override val offendingNode: ErrorNode,
                                    override val reason: ErrorReason,
                                    override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"postcondition.not.preserved.base.case"

  val r = s"$offendingNode".replaceAll("\\b(inhale|exhale)\\b", "").replaceAll(" +", " ").trim
  override val text = s"Postcondition $r might not be preserved in base case."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PostconditionNotPreservedBaseCase(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PostconditionNotPreservedBaseCase(offendingNode, r, cached)
}

case class PostconditionNotPreservedInductiveStep(override val offendingNode: ErrorNode,
                                             override val reason: ErrorReason,
                                             override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"postcondition.not.preserved.inductive.step"

  val r = s"$offendingNode".replaceAll("\\b(inhale|exhale)\\b", "").replaceAll(" +", " ").trim
  override val text = s"Postcondition $r might not be preserved in inductive step."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PostconditionNotPreservedInductiveStep(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PostconditionNotPreservedInductiveStep(offendingNode, r, cached)
}

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
