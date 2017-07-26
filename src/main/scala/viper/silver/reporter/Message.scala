/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.reporter

sealed trait Message {
  def toString: String
}

case class SuccessMessage(file: File, entity: Entity, verification_time: Time) extends Message
case class FailureMessage(file: File, entity: Entity, verification_time: Time, pos: Position) extends Message
//TODO: design the infrastructure for reporting Symbolic Execution info with variable level of detail.
case class SymbExLogRepport(file: File, entity: Entity, timestamp: Time, stuff: Option[Any]) extends Message
