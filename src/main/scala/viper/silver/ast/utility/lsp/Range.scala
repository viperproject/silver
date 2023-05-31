// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

import viper.silver.parser.Where
import viper.silver.ast.{AbstractSourcePosition, FilePosition, HasLineColumn}
import java.nio.file.Path
import viper.silver.ast.utility.lsp.SelectionBoundTrait
import viper.silver.ast.LineColumnPosition

/** A range  */
case class RangePosition(file: Path, var start: HasLineColumn, var _end: HasLineColumn)
  extends AbstractSourcePosition {
  var modified: Boolean = false
  override def end = Some(_end)

  def shiftStart(deltaLine: Int, deltaCol: Int): Unit =
    start = LineColumnPosition(start.line + deltaLine, start.column + deltaCol)
  def shiftEnd(deltaLine: Int, deltaCol: Int): Unit =
    _end = LineColumnPosition(_end.line + deltaLine, _end.column + deltaCol)
  def shiftInLine(delta: Int): Unit = {
    shiftStart(0, delta)
    shiftEnd(0, delta)
  }
}

object RangePosition {
  def apply(pos: AbstractSourcePosition): RangePosition =
    RangePosition(pos.file, pos.start, pos.end.getOrElse(pos.start))

  def apply(where: Where): Option[RangePosition] = where.pos match {
    case (fp1: FilePosition, fp2: FilePosition) if fp1.file == fp2.file => Some(RangePosition(fp1.file, fp1, fp2))
    case _ => None
  }

  def betweenEnds(startAfter: Where, endAfter: Where): Option[RangePosition] = (startAfter.pos._2, endAfter.pos._2) match {
    case (fp1: FilePosition, fp2: FilePosition) if fp1.file == fp2.file => Some(RangePosition(fp1.file, fp1, fp2))
    case _ => None
  }
}

trait BelongsToFile {
  def file: Path
}

trait SelectableInBound {
  val bound: SelectionBoundTrait
}
// trait SelectableInBound[+A <: SelectableInBound[A, T], +T <: SelectionBoundTrait] { this: A =>
//   val bound: T
//   def get: A = this
//   def selectableInScope: Option[SelectableInBound[A, _ <: SelectionBoundScopeTrait]] =
//     if (bound.isInstanceOf[SelectionBoundScopeTrait]) Some(this.asInstanceOf[SelectableInBound[A, _ <: SelectionBoundScopeTrait]]) else None
// }

trait HasRangePositions {
  def rangePositions: Seq[RangePosition]
}
