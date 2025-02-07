package viper.silver.plugin.standard.loopspecs



import viper.silver.ast.Position
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
  override val text = s"Precondition ${reason.offendingNode} might not hold on entry." //todo: might not be necess to have much info in text

  override val pos = reason.offendingNode.pos


  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PreconditionNotEstablished(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PreconditionNotEstablished(offendingNode, r, cached)
}

case class PreconditionNotPreserved(override val offendingNode: ErrorNode,
                                      override val reason: ErrorReason,
                                      override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"precondition.not.preserved"
  override val text = s"Precondition ${reason.offendingNode} might not be preserved."

  override val pos = reason.offendingNode.pos


  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PreconditionNotPreserved(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PreconditionNotPreserved(offendingNode, r, cached)
}

case class PostconditionNotPreservedBaseCase(override val offendingNode: ErrorNode,
                                    override val reason: ErrorReason,
                                    override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"postcondition.not.preserved.base.case"

  override val pos = reason.offendingNode.pos

  val r = s"${reason.offendingNode}".replaceAll("\\b(inhale|exhale)\\b", "").replaceAll(" +", " ").trim
  override val text = s"Postcondition $r might not be preserved in base case."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PostconditionNotPreservedBaseCase(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PostconditionNotPreservedBaseCase(offendingNode, r, cached)
}

case class PostconditionNotPreservedInductiveStep(override val offendingNode: ErrorNode,
                                             override val reason: ErrorReason,
                                             override val cached: Boolean = false) extends ExtensionAbstractVerificationError {
  override val id = s"postcondition.not.preserved.inductive.step"

  override val pos = reason.offendingNode.pos

  val r = s"${reason.offendingNode}".replaceAll("\\b(inhale|exhale)\\b", "").replaceAll(" +", " ").trim
  //Todo rm this replace probably not necessary anymore
  override val text = s"Postcondition $r might not be preserved in inductive step."

  override def withNode(offendingNode: errors.ErrorNode = this.offendingNode) =
    PostconditionNotPreservedInductiveStep(this.offendingNode, this.reason, this.cached)

  override def withReason(r: ErrorReason) = PostconditionNotPreservedInductiveStep(offendingNode, r, cached)
}

//TODO rm if unused! and change error msgs from rec
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
  override val text = s"$reason / ${reason.pos}/ ${reason.id} / ${reason.offendingNode} / ${reason.offendingNode.pos} / ${reason.offendingNode.errT}" //  s"Precondition $offendingNode might not be preserved in while loop. $reason. ${reason.pos}"
  //  Assertion b might not hold. / prec_not_preserved.vpr@7.9--7.19/ assertion.false / b / prec_not_preserved.vpr@7.9--7.19 / NoTrafos Assertion b might not hold. (prec_not_preserved.vpr@7.9--7.19)

  //TODO: b points to the b:= false line and not to the precond b
  //offNode = b:= Helper_(b)
  //reason = assertion b might not hold
  // reason.pos = offNode.pos = pos(b := Helper(b))

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
