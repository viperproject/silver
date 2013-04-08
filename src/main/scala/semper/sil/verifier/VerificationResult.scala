package semper.sil.verifier

import semper.sil.ast._

/** Describes the outcome of a verification attempt of a SIL program.
  *
  * @author Stefan Heule
  */
sealed trait VerificationResult

/** A successful verification. */
object Success extends VerificationResult {
  override def toString = "Verification successful."
}

/** A non-successful verification.
  *
  * @param errors The errors encountered during parsing, translation or verification.
  */
case class Failure(errors: Seq[AbstractError]) extends VerificationResult {
  override def toString = {
    s"Verification failed with ${errors.size} errors:\n  " +
      (errors map (e => e.toString)).mkString("\n  ")
  }
}

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

  override def toString = readableMessage + " " + readablePosition

  def readablePosition = pos match {
    case TranslatedPosition(file, RealPosition(line, _)) => s"(${file.getName}:${line})"
    case SourcePosition(line, _) => s"(${line})"
    case _ => ""
  }
}

/** A parser error. */
case class ParseError(message: String, pos: Position) extends AbstractError {
  def fullId = "parser.error"
  def readableMessage = s"$pos: Parse error: $message"
}

/** A typechecker error. */
case class TypecheckerError(message: String, pos: Position) extends AbstractError {
  def fullId = "typechecker.error"
  def readableMessage = s"$pos: $message"
}

/** An error during command-line option parsing. */
case class CliOptionError(message: String) extends AbstractError {
  def pos = NoPosition
  def fullId = "clioption.error"
  def readableMessage = s"Command-line interface: $message"
}
