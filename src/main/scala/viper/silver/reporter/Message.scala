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
  def toString: String
}

sealed trait VerificationResultMessage extends Message {
  def result: VerificationResult
}

object VerificationResultMessage {
  /** Create a [[VerificationResultMessage]], depending on the type of the provided `result`:
    * if `result` is [[Success]] then a [[SuccessMessage]] is created, otherwise (if `result` is
    * a [[Failure]]) a [[FailureMessage]] is created.
    */
  def apply(entity: Entity, verificationTime: Time, result: VerificationResult)
           : VerificationResultMessage = {
    
    result match {
      case Success => SuccessMessage(entity, verificationTime)
      case failure: Failure => FailureMessage(entity, verificationTime, failure)
    }
  }
}

case class SuccessMessage(entity: Entity, verificationTime: Time)
    extends VerificationResultMessage {

  val result: VerificationResult = Success
}

case class FailureMessage(entity: Entity, verificationTime: Time, result: Failure)
    extends VerificationResultMessage

// TODO: design the infrastructure for reporting Symbolic Execution info with variable level of detail.
case class SymbExLogReport(file: File, entity: Entity, timestamp: Time, stuff: Option[Any])
    extends Message

// FIXME: for debug purposes only: a pong message can be reported to indicate
// FIXME: that the verification backend is alive.
case class PongMessage(msg: String) extends Message
