package semper.sil.verifier

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.expressions.terms.FieldReadExpression
import semper.sil.ast.expressions.Expression
import semper.sil.ast.ASTNode

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

  case class Illformed(offendingNode: ASTNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "illformed"
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

  case class AssertionViolated(offendingNode: ASTNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "ass.violated"
    val text = "Assertion might not hold."
  }

  /* RFC: Would it be reasonable to have PostconditionViolated <: AssertionViolated? */
  case class PostconditionViolated(offendingNode: ASTNode, reason: ErrorReason) extends AbstractVerificationError {
    val id = "post.violated"
    val text = "Postcondition might not hold."
  }
}

object reasons {
  case class FeatureUnsupported(feature: ASTNode) extends AbstractErrorReason {
    val id = "feature.unsupported"
    override val offendingNode = Some(feature)

    def readableMessage = s"${feature.toString} is not supported."
  }

  case class ReceiverNull(receiver: Expression) extends AbstractErrorReason {
    val id = "receiver.null"
    override val offendingNode = Some(receiver)

    def readableMessage = s"The receiver $receiver might be null."
  }

  case class NegativeFraction(fraction: Expression) extends AbstractErrorReason {
    val id = "negative.fraction"
    override val offendingNode = Some(fraction)

    def readableMessage = s"The fraction $fraction might be negative."
  }
}