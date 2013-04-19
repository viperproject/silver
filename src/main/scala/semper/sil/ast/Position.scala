package semper.sil.ast

import java.io.File

/** A trait describing the position of occurance of an AST node. */
sealed trait Position

/** Describes ''no location'' for cases where a `Position` is expected, but not available. */
case object NoPosition extends Position {
  override def toString = "<no position>"
}

/** An actual position that has a line and column. */
trait RealPosition {
  def line: Int
  def column: Int
  override def toString = s"$line.$column"
}
object RealPosition {
  def unapply(pos: RealPosition) = Some(pos.line, pos.column)
}

/** Describes a location in a file by line and column number. */
case class SourcePosition(line: Int, column: Int) extends Position with RealPosition

/** Refers to a location in a source language that has been translated to SIL. */
case class TranslatedPosition(file: File, pos: RealPosition) extends Position with RealPosition {
  val line = pos.line
  val column = pos.column
  override def toString = s"${file.getName}:$line"
}
