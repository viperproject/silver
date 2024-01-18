// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

import viper.silver.parser.Where
import viper.silver.ast.{AbstractSourcePosition, FilePosition, HasLineColumn}
import java.nio.file.Path
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
  override def deltaColumn(delta: Int): RangePosition = {
    shiftInLine(delta)
    this
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

trait SuggestableInBound extends SelectableInBound {
  val suggestionBound: SuggestionBound
  val bound: SelectionBoundTrait = suggestionBound.bound
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

/** A position over the keyword within the scope will match.
 * A keyword of `None` implies that anything in the scope will match.
 * A scope of `None` implies that anything with the keyword will match.
 * If both are `None`, then *any* position will match!
*/
sealed trait SelectionBoundTrait extends HasRangePositions
case object SelectionBound extends SelectionBoundTrait {
  def rangePositions: Seq[RangePosition] = Nil
}

sealed trait SelectionBoundKeywordTrait extends SelectionBoundTrait {
  def keyword: String
}
case class SelectionBoundKeyword(keyword: String) extends SelectionBoundKeywordTrait {
  def rangePositions: Seq[RangePosition] = Nil
}

sealed trait SelectionBoundScopeTrait extends SelectionBoundTrait {
  def scope: RangePosition
  def rangePositions: Seq[RangePosition] = Seq(scope)
}
case class SelectionBoundScope(scope: RangePosition) extends SelectionBoundScopeTrait

case class SelectionBoundBoth(keyword: String, scope: RangePosition) extends SelectionBoundKeywordTrait with SelectionBoundScopeTrait
