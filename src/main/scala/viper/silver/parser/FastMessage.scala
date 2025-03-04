// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver

import viper.silver.ast.{SourcePosition, Position => ViperPosition}
import viper.silver.ast.FilePosition
import viper.silver.parser.PNode

import scala.util.parsing.input.Position

case class FastMessage (label : String, pos : SourcePosition, error: Boolean) {
  def line : Int = pos.line
  def column : Int = pos.column
}

object FastMessage {
  def apply(label: String, pos: Position): FastMessage = {
    pos match {
      case fpos: FilePosition => FastMessage(label, SourcePosition(fpos.file, pos.line, pos.column), true)
    }
  }
  def apply(label: String, pos: Position, error: Boolean): FastMessage = {
    pos match {
      case fpos: FilePosition => FastMessage(label, SourcePosition(fpos.file, pos.line, pos.column), error)
    }
  }
  def apply(label: String, pos: ViperPosition): FastMessage = {
    pos match {
      case spos: SourcePosition => FastMessage(label, spos, true)
      case _ => sys.error("Unexpected position type.")
    }
  }
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
  def message (value : PNode, msg : String, cond : Boolean = true, error : Boolean = true) : Messages =
    if (cond) {
      val valuePos = value.errorPosition match {
        case pos: SourcePosition => pos
        case other => sys.error(s"Unexpected position type: ${other} (${other.getClass()})")
      }
      aMessage (FastMessage (msg, valuePos, error))
    } else {
      noMessages
    }

  /**
    * Sort the messages by position in increasing order.
    */
   def sortmessages (messages : Messages) : Messages =
    messages.sortWith {
      case (msg1, msg2) =>
        (msg1.line < msg2.line) || ((msg1.line == msg2.line) && (msg1.column < msg2.column))
    }.distinct
}
