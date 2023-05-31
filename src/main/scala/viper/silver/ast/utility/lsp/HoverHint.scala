// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

/** A trait for PAst nodes which should display hover information in the IDE */
trait HasHoverHints {
  def getHoverHints: Seq[HoverHint]
}

case class HoverHint(
  /** The text hint to show when hovering */
  hint: String,
  /** Display the hover hint when this bound is met */
  bound: SelectionBoundTrait,
) extends SelectableInBound with HasRangePositions {
  override def rangePositions: Seq[RangePosition] = bound.rangePositions
}

/** A position over the keyword within the scope will match.
 * A keyword of `None` implies that anything in the scope will match.
 * A scope of `None` implies that anything with the keyword will match.
 * If both are `None`, then *any* position will match!
*/
sealed trait SelectionBoundTrait extends HasRangePositions
case class SelectionBound() extends SelectionBoundTrait {
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
