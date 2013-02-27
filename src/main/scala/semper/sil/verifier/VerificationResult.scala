package semper.sil.verifier

import semper.sil.ast.Position

/** Describes the outcome of a verification attempt of a SIL program.
  *
  * @author Stefan Heule
  */
sealed trait VerificationResult

/** A successful verification. */
object Success extends VerificationResult

/** A non-successful verification.
  *
  * @param errors The errors encountered during parsing, translation or verification.
  */
case class Failure(errors: Seq[AbstractError]) extends VerificationResult

/**
 * A common super-trait for errors that occur during parsing, translation or verification.
 */
trait AbstractError {
  /** The position where the error occured. */
  def pos: Position

  /** A short and unique identifier for this error. */
  def fullId: String

  /** A readable message describing the error. */
  def readableMessage: String
}

/** A parser error. */
case class ParseError(message: String, pos: Position) extends AbstractError {
  def fullId = "parser.error"
  def readableMessage = s"$pos: $message"
}

/** A typechecker error. */
case class TypecheckerError(message: String, pos: Position) extends AbstractError {
  def fullId = "typechecker.error"
  def readableMessage = s"$pos: $message"
}