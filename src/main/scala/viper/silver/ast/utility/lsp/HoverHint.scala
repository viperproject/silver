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
  /** The code hint to show when hovering (e.g. function signature).
   * Displayed in a code block. */
  hint: String,
  /** The text hint to show when hovering (e.g. documentation) */
  documentation: Option[String],
  // TODO: improve wording
  /** The range to highlight when hovering. If `None` then
    either the range of the hovered keyword (matching `bound`) is used
    or if the range of `bound` is met instead that is used. */
  highlight: Option[RangePosition],
  /** Display the hover hint when this bound is met */
  bound: SelectionBoundTrait,
) extends SelectableInBound with HasRangePositions {
  override def rangePositions: Seq[RangePosition] = highlight.toSeq ++ bound.rangePositions
}
