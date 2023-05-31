// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp
import viper.silver.ast.utility.lsp.SelectionBoundTrait

/** TODO */
trait HasGotoDefinitions {
  def getGotoDefinitions: Seq[GotoDefinition]
}

case class GotoDefinition(
  /** The position to go to when clicked */
  definition: RangePosition,
  /** Display the hover hint when this bound is met */
  bound: SelectionBoundTrait,
) extends SelectableInBound with HasRangePositions {
  override def rangePositions: Seq[RangePosition] = Seq(definition) ++ bound.rangePositions
}
