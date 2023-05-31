// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

/** TODO */
trait HasFoldingRanges {
  def getFoldingRanges: Seq[FoldingRange]
}

case class FoldingRange(
  range: RangePosition,
  /** If `true` then `range.start.column` is ignored and the default of
   * the length of the start line is used. */
  ignoreStartColumn: Boolean = false,
  /** If `true` then `range._end.column` is ignored and the default of
   * the length of the end line is used. */
  ignoreEndColumn: Boolean = false,
  /** Describes the kind of the folding range such as `comment` or `region`.
	 * The kind is used to categorize folding ranges and used by commands like
	 * 'Fold all comments'. Predefined kinds are: `"comment"`, `"imports"`, `"region"`. */
  kind: String = "region",
) extends HasRangePositions with BelongsToFile {
  override def rangePositions: Seq[RangePosition] = Seq(range)
  override def file = range.file
}
