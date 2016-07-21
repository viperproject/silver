package viper.silver

import scala.util.parsing.input.{NoPosition, Position}

/**
  * Created by Sahil on 22.06.16.
  */


case class FastMessage (label : String, pos : Position = NoPosition) {

  def line : Int = pos.line


  def column : Int = pos.column


//  def format : String = s"[${pos}] $label\n\n${pos.longString}"

}

object FastMessaging {

  type Messages = Seq[FastMessage]

  val noMessages = IndexedSeq.empty

  def aMessage (message : FastMessage) =
    IndexedSeq (message)

  def message (value : Any, msg : String, cond : Boolean = true) : Messages =
    if (cond)
      aMessage (FastMessage (msg, FastPositions.getStart (value)))
    else
      noMessages

   def sortmessages (messages : Messages) : Messages =
    messages.sortWith {
      case (msg1, msg2) =>
        (msg1.line < msg2.line) || ((msg1.line == msg2.line) && (msg1.column < msg2.column))
    }

}
