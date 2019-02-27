// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.verifier

import viper.silver.ast._

/** Describes the outcome of a verification attempt of a Viper program.

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
      (errors map (e => "[" + e.fullId + "] " + e.readableMessage)).mkString("\n  ")
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

  /* TODO: Simply looking for pos in message is rather fragile */
  override def toString = {
    val msg = readableMessage
    val posStr = pos.toString

    if (msg contains posStr) s"$msg"
    else s"$msg ($posStr)"
  }

  val cached: Boolean = false
}

abstract class ParseReport(message: String, pos: Position) extends AbstractError

/** A parser error. */
case class ParseError(message: String, override val pos: Position)
  extends ParseReport(message, pos) {
  def fullId = "parser.error"
  def readableMessage = s"Parse error: $message ($pos)"
}

/** A case class used for treating certain parser reports as non-critical. */
case class ParseWarning(message: String, override val pos: Position)
  extends ParseReport(message, pos) {
  def fullId = "parser.warning"
  def readableMessage = s"Parse warning: $message ($pos)"
}

/** An error during consistency-checking an AST node */
case class ConsistencyError(message: String, pos:Position) extends AbstractError {
  def fullId = "consistency.error"
  def readableMessage: String = s"Consistency error: $message ($pos)"
}

/** A typechecker error. */
case class TypecheckerError(message: String, pos: Position) extends AbstractError {
  def fullId = "typechecker.error"
  def readableMessage = s"$message ($pos)"
}

/** An error during command-line option parsing. */
case class CliOptionError(message: String) extends AbstractError {
  def pos = NoPosition
  def fullId = "clioption.error"
  def readableMessage = s"Command-line interface: $message"
}

/** An error indicating that a dependency couldn't be found. */
case class DependencyNotFoundError(message: String) extends AbstractError {
  def pos = NoPosition
  def fullId = "dependencynotfound.error"
  def readableMessage = s"Dependency not found: $message"
}

/* RFC: [Malte] If we want to be more fine-grained, for example, by having a
 *      timeout per method/member, or even per proof obligation, then we should
 *      consider subclassing AbstractVerificationError, or use an Internal error
 *      in combination with a TimeoutReason.
 */
case class TimeoutOccurred(n: Long, units: String) extends AbstractError {
  def pos = NoPosition
  def fullId = "timeout.error"
  def readableMessage = s"Timeout occurred after $n $units"
}

case class AbortedExceptionally(cause: Throwable) extends AbstractError {
  def pos = NoPosition
  def fullId = "exceptional.error"
  def readableMessage = s"Verification aborted exceptionally"
}
