/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.reporter

import viper.silver.verifier.{Failure, Success, VerificationResult}

/**
  * The only possible messages for the reporter are defined in this file.
  *
  * TODO: in case this file is modified, please remember to add/edit the Json
  * TODO:               converter(s) in `viper/server/ViperIDEProtocol.scala`.
  *
  */
sealed trait Message {
  override def toString: String = s"generic_message"
  val name: String
}

sealed trait VerificationResultMessage extends Message {
  override val name: String = s"verification_result"
  def result: VerificationResult
  val verifier: String
}

object VerificationResultMessage {
  /** Create a [[VerificationResultMessage]] concerning verification of a full program, depending on the type of the
    * provided `result`:
    *  if `result` is [[Success]] then an [[OverallSuccessMessage]] is created, otherwise (if `result` is
    *  a [[Failure]]) a [[OverallFailureMessage]] is created.
    */
  def apply(verifier: String, verificationTime: Time, result: VerificationResult)
  : VerificationResultMessage = {

    result match {
      case Success => OverallSuccessMessage(verifier, verificationTime)
      case failure: Failure => OverallFailureMessage(verifier, verificationTime, failure)
    }
  }

  /** Create a [[VerificationResultMessage]] concerning a particular program [[Entity]], depending on the type of the
    * provided `result`:
    *  if `result` is [[Success]] then an [[EntitySuccessMessage]] is created, otherwise (if `result`
    *  is a [[Failure]]) a [[EntityFailureMessage]] is created.
    */
  def apply(verifier: String, entity: Entity, verificationTime: Time, result: VerificationResult)
  : VerificationResultMessage = {

    result match {
      case Success => EntitySuccessMessage(verifier, entity, verificationTime)
      case failure: Failure => EntityFailureMessage(verifier, entity, verificationTime, failure)
    }
  }
}

// Overall results concern results for the entire program (e.g. those presently produced by the Carbon backend)
case class OverallSuccessMessage(verifier: String, verificationTime: Time)
  extends VerificationResultMessage {

  override def toString: String = s"overall_success_message(" +
    s"verifier=${verifier}, time=${verificationTime.toString()})"

  val result: VerificationResult = Success
}

case class OverallFailureMessage(verifier: String, verificationTime: Time, result: Failure)
  extends VerificationResultMessage {

  override def toString: String = s"overall_failure_message(" +
    s"verifier=${verifier}, time=${verificationTime.toString()}, result=${result.toString()})"
}

// Entity results concern results for specific program entities (these are presently produced by the Silicon backend)
case class EntitySuccessMessage(verifier: String, concerning: Entity, verificationTime: Time)
    extends VerificationResultMessage {

  override def toString: String = s"entry_success_message(" +
    s"verifier=${verifier}, " +
    s"concerning=${concerning.toString()}, time=${verificationTime.toString()})"

  val result: VerificationResult = Success
}

case class EntityFailureMessage(verifier: String, concerning: Entity, verificationTime: Time, result: Failure)
    extends VerificationResultMessage {

  override def toString: String = s"entry_failure_message(" +
    s"verifier=${verifier}, concerning=${concerning.toString()}, " +
    s"time=${verificationTime.toString()}, result=${result.toString()})"
}

case class StatisticsReport(nOfMethods: Int, nOfFunctions: Int, nOfPredicates: Int, nOfDomains: Int, nOfFields: Int)
    extends Message {

  override def toString: String = s"statistics_report(" +
    s"nom=${nOfMethods.toString()}, nofu=${nOfFunctions.toString()}, nop=${nOfPredicates.toString()}, " +
    s"nod=${nOfDomains.toString()}, nofi=${nOfFields.toString()})"

  override val name = s"statistics"
}

case class ProgramOutlineReport(members: List[Entity]) extends Message {

  override def toString: String = s"program_outline_report(members=${members.toString()})"
  override val name: String = s"program_outline"
}

case class ProgramDefinitionsReport(definitions: List[Definition]) extends Message {

  override def toString: String = s"program_definitions_report(definitions=${definitions.toString()}"
  override val name: String = s"program_definitions"
}

// TODO: design the infrastructure for reporting Symbolic Execution info with variable level of detail.
case class SymbExLogReport(entity: Entity, timestamp: Time, stuff: Option[Any])
    extends Message {

  override def toString: String = s"symbolic_execution_logger_report(" +
    s"entity=${entity.toString()}, " +
    s"timestamp=${timestamp.toString()}, stuff=${stuff.toString()})"

  override val name: String = s"symbolic_execution_logger_report"
}

case class ExceptionReport(e: java.lang.Throwable) extends Message {

  override def toString: String = s"exception_report(e=${e.toString()})"

  override val name: String = s"exception_report"
}

// FIXME: for debug purposes only: a pong message can be reported to indicate
// FIXME: that the verification backend is alive.
case class PongMessage(msg: String) extends Message {

  override def toString: String = s"dbg__pong(msg=$msg)"
  override val name: String = s"dbg__pong"
}
