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
  def location: SourceLocation = offendingNode.sourceLocation
}

abstract class ErrorReason {
  def id: String
  def offendingNode: Option[ASTNode] = None
  def location: Option[SourceLocation] = offendingNode map (_.sourceLocation)
}

object errors {
}

object reasons {
  case class ReceiverMightBeNull(receiver: Expression) extends ErrorReason {
    val id = "receiver.null"
    override val offendingNode = Some(receiver)

    def readableMessage = s"The receiver $receiver might be null."
  }
}