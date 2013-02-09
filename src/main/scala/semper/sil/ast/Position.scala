package semper.sil.ast

/** A trait describing the position of occurance of an AST node. */
sealed trait Position

/** Describes ''no location'' for cases where a `Position` is expected, but not available. */
case object NoPosition extends Position

/** Describes a location in a file by line and column number. */
case class SourcePosition(line: Int, column: Int) extends Position
