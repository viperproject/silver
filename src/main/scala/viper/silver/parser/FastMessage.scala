// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver

import scala.util.parsing.input.{NoPosition, Position}

case class FastMessage (label : String, pos : Position = NoPosition) {

  def line : Int = pos.line


  def column : Int = pos.column

}

/**
  * Support for Messages in FastParser. Messages are finally kept
  * as a sequence and sorted before display
  * */

object FastMessaging {

  type Messages = Seq[FastMessage]

  val noMessages = IndexedSeq.empty

  def aMessage (message : FastMessage) =
    IndexedSeq (message)

   /**
    * Makes a message list if cond is true. Stored with the position of the value
    */
  def message (value : Any, msg : String, cond : Boolean = true) : Messages =
    if (cond)
      aMessage (FastMessage (msg, FastPositions.getStart (value)))
    else
      noMessages

  /**
    * Sort the messages by position in increasing order.
    */
   def sortmessages (messages : Messages) : Messages =
    messages.sortWith {
      case (msg1, msg2) =>
        (msg1.line < msg2.line) || ((msg1.line == msg2.line) && (msg1.column < msg2.column))
    }
}
