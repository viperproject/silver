// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast

import viper.silver.utility.Common.StructuralEquality
import java.nio.file.Path

import viper.silver.parser.FastParser

/** A trait describing the position of occurrence of an AST node. */
sealed trait Position {
  def deltaColumn(delta: Int): Position
}

/** Describes ''no location'' for cases where a `Position` is expected, but not available. */
case object NoPosition extends Position {
  override def deltaColumn(delta: Int) = this
  override def toString = "<no position>"
}

/** A position that references a line and a column. */
trait HasLineColumn extends Position {
  def line: Int

  def column: Int

  def <=(other: HasLineColumn): Boolean = {
    if (line < other.line) true
    else if (line > other.line) false
    else column <= other.column
  }

  def deltaColumn(delta: Int): HasLineColumn
  override def toString = s"$line.$column"
}

/** A position that references an identifier, intended to be used
  * by frontends to identify the origin of a node.
  */
trait HasIdentifier extends HasLineColumn {
  def id: String
}

case class LineColumnPosition(line: Int, column: Int) extends HasLineColumn {
  override def deltaColumn(delta: Int) = LineColumnPosition(line, column + delta)
}

/** Represents a source code position by referencing a file, a line and a column.
  * Optionally, an additional end position can be specified.
  */
trait AbstractSourcePosition extends HasLineColumn {
  def file: Path

  def start: HasLineColumn

  def end: Option[HasLineColumn]

  lazy val line: Int = start.line
  lazy val column: Int = start.column

  private def fileComponent: String =
    if (file == null || file.getFileName == null) ""
    else file.getFileName.toString + "@"

  private def lineColComponent(lc_pos: HasLineColumn) =
    s"${lc_pos.line}.${lc_pos.column}"

  override def deltaColumn(delta: Int): AbstractSourcePosition
  override def toString: String = end match {
    case None =>
      s"$fileComponent${lineColComponent(start)}"
    case Some(end_pos) =>
      s"$fileComponent${lineColComponent(start)}--${lineColComponent(end_pos)}"
  }
}

object AbstractSourcePosition {
  def unapply(pos: AbstractSourcePosition): Option[(Int, Int)] =
    Some(pos.line, pos.column)
}

/** An implementation of [[AbstractSourcePosition]].
  *
  * @param file  Source file.
  * @param start Start position in the source file.
  * @param end   Optional end position in the source file.
  */
class SourcePosition(val file: Path, val start: HasLineColumn, val end: Option[HasLineColumn])
  extends AbstractSourcePosition with StructuralEquality {

  override def deltaColumn(delta: Int): SourcePosition =
    new SourcePosition(file, start.deltaColumn(delta), end.map(_.deltaColumn(delta)))
  protected val equalityDefiningMembers: Seq[Object] =
    file :: start :: end :: Nil
}

class IdentifierPosition(val file: Path, val start: HasLineColumn, val end: Option[HasLineColumn], val id: String)
  extends AbstractSourcePosition with StructuralEquality with HasIdentifier {
  override def deltaColumn(delta: Int): IdentifierPosition =
    new IdentifierPosition(file, start.deltaColumn(delta), end.map(_.deltaColumn(delta)), id)
  protected val equalityDefiningMembers: Seq[Object] =
    file :: start :: end :: id :: Nil
}

class LineCol(fp: FastParser) {
  def getPos(index: Int): (Int, Int) = {
    val line_offset = fp._line_offset
    if (line_offset.isEmpty) {
      return (1, 1);
    }
    val result = java.util.Arrays.binarySearch(line_offset, index)
    if (result >= 0) {
      // Exact match
      val line = result
      (line + 1, index - line_offset(line) + 1)
    } else {
      // The binary search returned `- insertionPoint - 1`
      val line = -result - 2
      (line + 1, index - line_offset(line) + 1)
    }
  }
}

object SourcePosition {
  def apply(file: Path, line: Int, column: Int) =
    new SourcePosition(file, LineColumnPosition(line, column), None)

  def apply(file: Path, start: HasLineColumn, end: HasLineColumn) =
    new SourcePosition(file, start, Some(end))

  def unapply(sp: SourcePosition): Option[(Path, HasLineColumn, Option[HasLineColumn])] =
    Some((sp.file, sp.start, sp.end))
}

/** Refers to a position in a source language that has been translated to Silver. */
case class TranslatedPosition(pos: AbstractSourcePosition) extends AbstractSourcePosition {
  val file: Path = pos.file
  val start: HasLineColumn = pos.start
  val end: Option[HasLineColumn] = pos.end
  override def deltaColumn(delta: Int): TranslatedPosition =
    new TranslatedPosition(pos.deltaColumn(delta))
}

case class FilePosition(file: Path, vline: Int, col: Int) extends util.parsing.input.Position with HasLineColumn {
  override lazy val line: Int = vline
  override lazy val column: Int = col
  override lazy val lineContents: String = toString
  override lazy val toString: String = s"${file.getFileName}@$vline.$col"
  override def deltaColumn(delta: Int): FilePosition = FilePosition(file, vline, col + delta)
}
object FilePosition {
  def apply(pos: (Int, Int))(implicit file: Path): FilePosition = FilePosition(file, pos._1, pos._2)
}

/**
  * A virtual position that can be used for nodes that do not naturally have a position like, e.g., synthesized nodes.
  *
  * @param identifier The string identifying the position.
  */
case class VirtualPosition(identifier: String) extends Position {
  override def toString: String = identifier
  override def deltaColumn(delta: Int): VirtualPosition = this
}
