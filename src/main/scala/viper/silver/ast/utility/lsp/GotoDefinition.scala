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
  /** The range enclosing this symbol (e.g. a function signature and body) */
  target: RangePosition,
  /** The position to go to when clicked (must be contained in `range`) */
  targetSelection: RangePosition,
  bound: SelectionBoundTrait,
) extends SelectableInBound with HasRangePositions {
  override def rangePositions: Seq[RangePosition] = Seq(target, targetSelection) ++ bound.rangePositions
}
