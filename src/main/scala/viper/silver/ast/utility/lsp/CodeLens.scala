// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

trait HasCodeLens {
  def getCodeLens: Seq[CodeLens]
}

case class CodeLens(
    /** The range in which this code lens is valid. Should only span a single line. */
    range: RangePosition,
    /** The command this code lens represents. */
    command: String,
) extends HasRangePositions with BelongsToFile {
  override def rangePositions: Seq[RangePosition] = Seq(range)
  override def file = range.file
}
