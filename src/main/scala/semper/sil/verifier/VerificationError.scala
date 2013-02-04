package semper.sil.verifier

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.expressions.Expression
import semper.sil.ast.ASTNode
import semper.sil.ast.methods.implementations.{UnfoldStatement, FoldStatement}

/** A case class to describe an error during the verification of a SIL program.
  *
  * @author Stefan Heule
  */
abstract class VerificationError {
  def id: String
  def offendingNode: ASTNode
  def reason: ErrorReason
  def readableMessage: String
  def sourceLocation: SourceLocation
}

abstract class ErrorReason {
  def id: String
  def offendingNode: Option[ASTNode]
  def sourceLocation: Option[SourceLocation]
  def readableMessage: String
}

abstract class AbstractVerificationError extends VerificationError {
  def text: String

  val sourceLocation = offendingNode.sourceLocation
  val readableMessage = s"[$sourceLocation]: $text ${reason.readableMessage}"
  override val toString = readableMessage
}

abstract class AbstractErrorReason extends ErrorReason {
  val sourceLocation = offendingNode map (_.sourceLocation)
  override val toString = readableMessage
}

object errors {
  case class Internal(offendingNode: ASTNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "internal"
    val text = "An internal error occurred."
  }

  case class AssertionMalformed(offendingNode: Expression, reason: ErrorReason) extends AbstractVerificationError {
    val id = "ass.malformed"
    val text = "$offendingNode is not well-formed."
  }

  /* TODO: Narrow down the type of offendingNode to something like Invokable, which would be
   *       a subtype of procedures and functions. We could then refine the error message to
   *       say something like "Invocation of <offendingNode.receiver>.<offendingNode.name> failed.".
   */
  case class InvocationFailed(offendingNode: ASTNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "call.failed"
    val text = "Invocation of $offendingNode failed."
  }

  case class AssertionViolated(offendingNode: Expression, reason: ErrorReason) extends AbstractVerificationError {
    val id = "ass.violated"
    val text = "Assertion might not hold."
  }

  /* RFC: Would it be reasonable to have PostconditionViolated <: AssertionViolated? */
  case class PostconditionViolated(offendingNode: Expression, reason: ErrorReason) extends AbstractVerificationError {
    val id = "post.violated"
    val text = "Postcondition might not hold."
  }

  case class FoldFailed(offendingNode: FoldStatement, reason: ErrorReason) extends AbstractVerificationError {
    val id = "fold.failed"
    val text = "Folding ${offendingNode.location} failed."
  }

  case class UnfoldFailed(offendingNode: UnfoldStatement, reason: ErrorReason) extends AbstractVerificationError {
    val id = "unfold.failed"
    val text = "Unfolding ${offendingNode.location} failed."
  }

  case class LoopInvariantNotPreserved(offendingNode: Expression, reason: ErrorReason) extends AbstractVerificationError {
    val id = "loopinv.not.preserved"
    val text = "Loop invariant might not be preserved."
  }

  case class LoopInvariantNotEstablished(offendingNode: Expression, reason: ErrorReason) extends AbstractVerificationError {
    val id = "loopinv.not.established"
    val text = "Loop invariant might not hold on entry."
  }
}

object reasons {
  case class FeatureUnsupported(feature: ASTNode) extends AbstractErrorReason {
    val id = "feature.unsupported"
    override val offendingNode = Some(feature)

    def readableMessage = s"${feature.toString} is not supported."
  }

  case class AssertionFalse(assertion: ASTNode) extends AbstractErrorReason {
    val id = "ass.false"
    override val offendingNode = Some(assertion)

    def readableMessage = "Assertion might not hold."
  }

  case class ReceiverNull(receiver: Expression) extends AbstractErrorReason {
    val id = "rcvr.null"
    override val offendingNode = Some(receiver)

    def readableMessage = s"Receiver $receiver might be null."
  }

  case class NegativeFraction(fraction: Expression) extends AbstractErrorReason {
    val id = "negative.fraction"
    override val offendingNode = Some(fraction)

    def readableMessage = s"Fraction $fraction might be negative."
  }

  case class InsufficientPermissions(where: Expression) extends AbstractErrorReason {
    val id = "insufficient.permissions"
    override val offendingNode = Some(where)

    def readableMessage = "Insufficient permissions to access $where."
  }
}