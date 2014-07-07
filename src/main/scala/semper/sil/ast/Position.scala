/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.sil.ast

import java.io.File
import java.nio.file.Path

/** A trait describing the position of occurrence of an AST node. */
sealed trait Position

/** Describes ''no location'' for cases where a `Position` is expected, but not available. */
case object NoPosition extends Position {
  override def toString = "<no position>"
}

/** An actual position that has a line and column. */
trait RealPosition {
  def file: Path
  def line: Int
  def column: Int
  override def toString = s"${if(file==null || file.getFileName==null) "" else file.getFileName.toString},$line:$column"
}
object RealPosition {
  def unapply(pos: RealPosition) = Some(pos.line, pos.column)
}

/** Describes a location in a file by line and column number. */
case class SourcePosition(file: Path, line: Int, column: Int) extends Position with RealPosition

/** Refers to a location in a source language that has been translated to SIL. */
case class TranslatedPosition(pos: RealPosition) extends Position with RealPosition {
  val line = pos.line
  val column = pos.column
  val file = pos.file
}
