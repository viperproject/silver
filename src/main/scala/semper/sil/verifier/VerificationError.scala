package semper.sil.verifier

import semper.sil.ast._

trait ErrorMessage {
  type PositionedNode = Node with Positioned
  def id: String
  def offendingNode: PositionedNode
  def pos: Position
  def readableMessage: String
}

trait VerificationError extends AbstractError with ErrorMessage {
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
    val text = s"$offendingNode might not be well-formed."
  }

  def AssertionMalformed(offendingNode: PositionedNode): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => AssertionMalformed(offendingNode, reason))

  case class MethodCallFailed(offendingNode: MethodCall, reason: ErrorReason) extends AbstractVerificationError {
    val id = "call.failed"
    val text = s"Method call of ${offendingNode.rcv}.${offendingNode.method.name} might fail."
  }

  def MethodCallFailed(offendingNode: MethodCall): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => MethodCallFailed(offendingNode, reason))

  case class ExhaleFailed(offendingNode: Exhale, reason: ErrorReason) extends AbstractVerificationError {
    val id = "exhale.failed"
    val text = "Exhale might fail."
  }

  def ExhaleFailed(offendingNode: Exhale): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => ExhaleFailed(offendingNode, reason))

  case class PostconditionViolated(offendingNode: Exp, member: Contracted, reason: ErrorReason) extends AbstractVerificationError {
    val id = "post.violated"
    val text = s"Postcondition of ${member.name} might not hold."
  }

  def PostconditionViolated(offendingNode: Exp, member: Contracted): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => PostconditionViolated(offendingNode, member, reason))

  case class FoldFailed(offendingNode: Fold, reason: ErrorReason) extends AbstractVerificationError {
    val id = "fold.failed"
    val text = s"Folding ${offendingNode.acc.loc} might fail."
  }
  
  def FoldFailed(offendingNode: Fold): PartialVerificationError =
    PartialVerificationError((reason: ErrorReason) => FoldFailed(offendingNode, reason))

  case class UnfoldFailed(offendingNode: Unfold, reason: ErrorReason) extends AbstractVerificationError {
    val id = "unfold.failed"
    val text = s"Unfolding ${offendingNode.acc.loc} might fail."
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

  case class AssertionFalse(offendingNode: Exp) extends AbstractErrorReason {
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