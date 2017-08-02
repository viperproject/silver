/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.reporter

sealed trait Message {
  def toString: String
}

/**
  * The only possible messages for the reporter are defined in this file.
  *
  * TODO: in case this file is modified, please remember to add/edit the Json
  * TODO:               converter(s) in `viper/server/ViperIDEProtocol.scala`.
  *
 */
case class SuccessMessage(file: File, entity: Entity, verification_time: Time) extends Message
case class FailureMessage(file: File, entity: Entity, verification_time: Time, pos: Position) extends Message
// TODO: design the infrastructure for reporting Symbolic Execution info with variable level of detail.
case class SymbExLogReport(file: File, entity: Entity, timestamp: Time, stuff: Option[Any]) extends Message

// FIXME: for debug purposes only: a pong message can be reported to indicate
// FIXME: that the verification backend is alive.
case class PongMessage(msg: String) extends Message
