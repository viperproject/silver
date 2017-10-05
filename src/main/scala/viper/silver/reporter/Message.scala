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
}

sealed trait VerificationResultMessage extends Message {
  override def toString: String = s"verification_result"
  def result: VerificationResult
}

object VerificationResultMessage {
  /** Create a [[VerificationResultMessage]] concerning verification of a full program, depending on the type of the provided `result`:
    * if `result` is [[Success]] then an [[OverallSuccessMessage]] is created, otherwise (if `result` is
    * a [[Failure]]) a [[OverallFailureMessage]] is created.
    */
  def apply(verificationTime: Time, result: VerificationResult)
  : VerificationResultMessage = {

    result match {
      case Success => OverallSuccessMessage(verificationTime)
      case failure: Failure => OverallFailureMessage(verificationTime, failure)
    }
  }

  /** Create a [[VerificationResultMessage]] concerning a particular program [[Entity]], depending on the type of the provided `result`:
    * if `result` is [[Success]] then an [[EntitySuccessMessage]] is created, otherwise (if `result` is
    * a [[Failure]]) a [[EntityFailureMessage]] is created.
    */
  def apply(entity: Entity, verificationTime: Time, result: VerificationResult)
  : VerificationResultMessage = {

    result match {
      case Success => EntitySuccessMessage(entity, verificationTime)
      case failure: Failure => EntityFailureMessage(entity, verificationTime, failure)
    }
  }
}

// Overall results concern results for the entire program (e.g. those presently produced by the Carbon backend)
case class OverallSuccessMessage(verificationTime: Time)
  extends VerificationResultMessage {

  val result: VerificationResult = Success
}

case class OverallFailureMessage(verificationTime: Time, result: Failure)
  extends VerificationResultMessage

// Entity results concern results for specific program entities (these are presently produced by the Silicon backend)
case class EntitySuccessMessage(concerning: Entity, verificationTime: Time)
    extends VerificationResultMessage {

  val result: VerificationResult = Success
}

case class EntityFailureMessage(entity: Entity, verificationTime: Time, result: Failure)
    extends VerificationResultMessage

// TODO: design the infrastructure for reporting Symbolic Execution info with variable level of detail.
case class SymbExLogReport(entity: Entity, timestamp: Time, stuff: Option[Any])
    extends Message {

  override def toString: String = s"symbolic_execution_logger_report"
}

// FIXME: for debug purposes only: a pong message can be reported to indicate
// FIXME: that the verification backend is alive.
case class PongMessage(msg: String) extends Message {

  override def toString: String = s"dbg__pong_message"
}
