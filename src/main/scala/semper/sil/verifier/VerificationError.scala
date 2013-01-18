package semper.sil.verifier

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.expressions.terms.FieldReadExpression
import semper.sil.ast.ASTNode

/** A case class to describe an error during the verification of a SIL program.
  *
  * @author Stefan Heule
  */
abstract class VerificationError(val id: String, val offendingNode: ASTNode) {
  def readableMessage(): String
  def location: SourceLocation = offendingNode.sourceLocation
}

// Example of an error (not used yet):
case class NullFieldRead(fieldAccess: FieldReadExpression) extends VerificationError("null.field.read", fieldAccess) {
  def readableMessage = {
    "The receiver in the expression %s might be null.".format(fieldAccess)
  }
}
