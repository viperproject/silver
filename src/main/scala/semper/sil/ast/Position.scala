package semper.sil.ast

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

/** Describes a location in a file by line and column number. */
case class SourcePosition(line: Int, column: Int) extends Position with RealPosition

/** Refers to a location in a source language that has been translated to SIL. */
case class TranslatedPosition(pos: RealPosition) extends Position with RealPosition {
  def line = pos.line
  def column = pos.column
}
