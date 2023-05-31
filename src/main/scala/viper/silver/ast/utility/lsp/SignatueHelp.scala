// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

/** TODO */
trait HasSignatureHelps {
  def getSignatureHelps: Seq[SignatureHelp]
}

case class SignatureHelp(
  bound: SelectionBoundTrait,
  help: Seq[SignatureHelpPart],
) extends SelectableInBound with HasRangePositions {
  override def rangePositions: Seq[RangePosition] = bound.rangePositions
}

case class SignatureHelpPart(isArgument: Boolean, text: String)
