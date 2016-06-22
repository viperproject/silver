package viper.silver

import scala.util.parsing.input.{NoPosition, Position}

/**
  * Created by sahil on 22.06.16.
  */


case class FastMessage (label : String, pos : Position = NoPosition) {


  def line : Int =
    pos.line


  def column : Int =
    pos.column


  def format : String =
    s"[${pos}] $label\n\n${pos.longString}"

}

object FastMessaging {

  type ==>[T,U] = PartialFunction[T,U]

// Seq of messages
  type Messages = Seq[FastMessage]


  val noMessages = IndexedSeq.empty

  /**
    * Make a sequence of messages from a single message.
    */
  def aMessage (message : FastMessage) =
    IndexedSeq (message)

  /**
    * If `f` is defined at `t` apply it and return the resulting sequence
    * of messages. Otherwise, return an empty sequence.
    */
  def check[T] (t : T) (f : T ==> Messages) : Messages =
    f.applyOrElse (t, (_ : T) => noMessages)



  def message[T] (value : T, msg : String, cond : Boolean = true) : Messages =
    if (cond)
      aMessage (FastMessage (msg, FastPositions.getStart (value)))
    else
      noMessages


   def sortmessages (messages : Messages) : Messages =
    messages.sortWith {
      case (msg1, msg2) =>
        (msg1.line < msg2.line) ||
          ((msg1.line == msg2.line) && (msg1.column < msg2.column))
    }



}
