package semper.sil.verifier

import semper.sil.ast._

trait ErrorMessage {
  type PositionedNode = Node with Positioned
  def id: String
  def offendingNode: PositionedNode
  def pos: Position
  def readableMessage: String
}

trait VerificationError extends ErrorMessage {
  def reason: ErrorReason
  def readableMessage(full: Boolean): String
  override def readableMessage = readableMessage(false)
  def fullId = s"$id:${reason.id}"
}

trait ErrorReason extends ErrorMessage

case class PartialVerificationError(f: ErrorReason => VerificationError) {
  private object DummyReason extends AbstractErrorReason {
    val id = "?"
    val readableMessage = "?"

    val offendingNode = new Node with Positioned {
      val pos = NoPosition
    }
  }

  def dueTo(reason: ErrorReason) = f(reason)
  override lazy val toString = f(DummyReason).readableMessage(true)
}

abstract class AbstractVerificationError extends VerificationError {
  protected def text: String

  def pos = offendingNode.pos

  def readableMessage(full: Boolean = true) = {
    val id = if (full) s" [$fullId]" else ""
    s"$pos:$id $text ${reason.readableMessage}"
  }

  override def toString = readableMessage(true)
}

abstract class AbstractErrorReason extends ErrorReason {
  def pos = offendingNode.pos
  override def toString = readableMessage
}

object errors {
  type PositionedNode = Node with Positioned
  case class Internal(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "internal"
    val text = "An internal error occurred."
  }

  def Internal(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => Internal(offendingNode, reason))
  
  case class UnsafeCode(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "unsafe"
    val text = "Unsafe code found."
  }
  
  def UnsafeCode(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => UnsafeCode(offendingNode, reason))

  case class AssertionMalformed(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "ass.malformed"
    val text = s"$offendingNode is not well-formed."
  }

  def AssertionMalformed(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssertionMalformed(offendingNode, reason))

  /* TODO: Narrow down the type of offendingNode to something like Invokable, which would be
   *       a subtype of procedures and functions. We could then refine the error message to
   *       say something like "Invocation of <offendingNode.receiver>.<offendingNode.name> failed.".
   */
  case class InvocationFailed(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "call.failed"
    val text = s"Invocation of $offendingNode failed."
  }

  def InvocationFailed(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => InvocationFailed(offendingNode, reason))

  case class AssertionViolated(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "ass.violated"
    val text = "Assertion might not hold."
  }

  def AssertionViolated(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssertionViolated(offendingNode, reason))

  /* RFC: Would it be reasonable to have PostconditionViolated <: AssertionViolated? */
  case class PostconditionViolated(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "post.violated"
    val text = "Postcondition might not hold."
  }
  
  def PostconditionViolated(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PostconditionViolated(offendingNode, reason))

  case class FoldFailed(offendingNode: Fold, reason: ErrorReason) extends AbstractVerificationError {
    val id = "fold.failed"
    val text = s"Folding ${offendingNode.acc.loc} failed."
  }
  
  def FoldFailed(offendingNode: Fold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FoldFailed(offendingNode, reason))

  case class UnfoldFailed(offendingNode: Unfold, reason: ErrorReason) extends AbstractVerificationError {
    val id = "unfold.failed"
    val text = s"Unfolding ${offendingNode.acc.loc} failed."
  }
  
  def UnfoldFailed(offendingNode: Unfold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => UnfoldFailed(offendingNode, reason))

  case class LoopInvariantNotPreserved(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "loopinv.not.preserved"
    val text = "Loop invariant might not be preserved."
  }
  
  def LoopInvariantNotPreserved(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotPreserved(offendingNode, reason))

  case class LoopInvariantNotEstablished(offendingNode: PositionedNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "loopinv.not.established"
    val text = "Loop invariant might not hold on entry."
  }
  
  def LoopInvariantNotEstablished(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => LoopInvariantNotEstablished(offendingNode, reason))
}

object reasons {
  type PositionedNode = Node with Positioned
  case class FeatureUnsupported(offendingNode: PositionedNode) extends AbstractErrorReason {
    val id = "feature.unsupported"
    def readableMessage = s"$offendingNode is not supported."
  }

  case class AssertionFalse(offendingNode: PositionedNode) extends AbstractErrorReason {
    val id = "ass.false"
    def readableMessage = s"Assertion $offendingNode might not hold."
  }

  case class ReceiverNull(offendingNode: PositionedNode) extends AbstractErrorReason {
    val id = "rcvr.null"
    def readableMessage = s"Receiver $offendingNode might be null."
  }

  case class NegativeFraction(offendingNode: PositionedNode) extends AbstractErrorReason {
    val id = "negative.fraction"
    def readableMessage = s"Fraction $offendingNode might be negative."
  }

  case class InsufficientPermissions(offendingNode: PositionedNode) extends AbstractErrorReason {
    val id = "insufficient.permissions"
    def readableMessage = s"Insufficient permissions to access $offendingNode."
  }
}