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

case class PostconditionNotPreservedWhileLoop(override val offendingNode: ErrorNode,
                                                  override val reason: ErrorReason,
                                                  override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"postcondition.not.preserved.while.loop"
  override val text = s"Postcondition $offendingNode might not be preserved in while loop."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PostconditionNotPreservedWhileLoop(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PostconditionNotPreservedWhileLoop(offendingNode, r, cached)
}
//todo correct names for above and below??
case class PreconditionNotPreservedWhileLoop(override val offendingNode: ErrorNode,
                                              override val reason: ErrorReason,
                                              override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"precondition.not.preserved.while.loop"
  override val text = s"Precondition $offendingNode might not be preserved in while loop."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PreconditionNotPreservedWhileLoop(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PreconditionNotPreservedWhileLoop(offendingNode, r, cached)
}

case class PreconditionNotEstablishedWhileLoop(override val offendingNode: ErrorNode,
                                             override val reason: ErrorReason,
                                             override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"precondition.not.established.while.loop"
  override val text = s"Precondition $offendingNode might not hold on entry. $reason. ${reason.pos}"

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PreconditionNotEstablishedWhileLoop(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PreconditionNotEstablishedWhileLoop(offendingNode, r, cached)
}
