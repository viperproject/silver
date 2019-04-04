// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast

import viper.silver.utility.Common.StructuralEquality
import fastparse.all._
import fastparse.StringReprOps
import java.nio.file.Path

/** A trait describing the position of occurrence of an AST node. */
sealed trait Position

/** Describes ''no location'' for cases where a `Position` is expected, but not available. */
case object NoPosition extends Position {
  override def toString = "<no position>"
}

/** A position that references a line and a column. */
trait HasLineColumn extends Position {
  def line: Int
  def column: Int
  override def toString = s"$line.$column"
}

/** A position that references an identifier, intended to be used
  * by frontends to identify the origin of a node.
  */
trait HasIdentifier extends HasLineColumn {
  def id: String
}

case class LineColumnPosition(line: Int, column: Int) extends HasLineColumn

/** Represents a source code position by referencing a file, a line and a column.
  * Optionally, an additional end position can be specified.
  */
trait AbstractSourcePosition extends HasLineColumn {
  def file: Path
  def start: HasLineColumn
  def end: Option[HasLineColumn]

  lazy val line = start.line
  lazy val column = start.column

  override def toString =
    s"${if(file==null || file.getFileName==null) "" else file.getFileName.toString + "@"}$line.$column"
}

object AbstractSourcePosition {
  def unapply(pos: AbstractSourcePosition) = Some(pos.line, pos.column)
}

/** An implementation of [[AbstractSourcePosition]].
  *
  * @param file Source file.
  * @param start Start position in the source file.
  * @param end Optional end position in the source file.
  */
class SourcePosition(val file: Path, val start: HasLineColumn, val end: Option[HasLineColumn])
    extends AbstractSourcePosition with StructuralEquality {

  protected val equalityDefiningMembers = file :: start :: end :: Nil
}

class IdentifierPosition(val file: Path, val start: HasLineColumn, val end: Option[HasLineColumn], val id: String)
  extends AbstractSourcePosition with StructuralEquality with HasIdentifier {
  protected val equalityDefiningMembers = file :: start :: end :: id :: Nil
}

object LineCol {
  def apply(input: ParserInput, index: Int) = {
    val Array(line, column) = StringReprOps.prettyIndex(input, index).split(":")
    (line.toInt, column.toInt)
  }
}

object SourcePosition {
  def apply(file: Path, line: Int, column: Int) =
    new SourcePosition(file, LineColumnPosition(line, column), None)

  def apply(file: Path, start: HasLineColumn, end: HasLineColumn) =
    new SourcePosition(file, start, Some(end))

  def unapply(sp: SourcePosition) = Some((sp.file, sp.start, sp.end))
}

/** Refers to a position in a source language that has been translated to Silver. */
case class TranslatedPosition(pos: AbstractSourcePosition) extends AbstractSourcePosition {
  val file = pos.file
  val start = pos.start
  val end = pos.end
}

