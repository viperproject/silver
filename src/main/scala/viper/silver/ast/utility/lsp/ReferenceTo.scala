// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

/** TODO */
trait HasReferenceTos {
  def getReferenceTos: Seq[ReferenceTo]
}

case class ReferenceTo(
  /** The definition referred to */
  to: RangePosition,
  /** The reference */
  from: RangePosition,
) extends HasRangePositions with BelongsToFile {
  override def file = to.file
  override def rangePositions: Seq[RangePosition] = Seq(to, from)
}
