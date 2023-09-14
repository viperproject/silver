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
  /** This sequence is concatenated to form the help which is
   * displayed when typing a call to the signature. */
  help: Seq[SignatureHelpPart],
  /** The documentation that is displayed under the signature help. */
  documentation: Option[String],
  /** Where this signature help is displayed. A `SelectionBoundKeywordTrait`
   * or above is highly recommended. */
  bound: SelectionBoundTrait,
) extends HasRangePositions with SelectableInBound {
  override def rangePositions: Seq[RangePosition] = bound.rangePositions
}

case class SignatureHelpPart(
  /** If this should be highlighted as an argument. The index of the
   * argument is calculated as the sum of all prior `SignatureHelp.help`s
   * which have `isArgument` set. */
  isArgument: Boolean,
  /** The text fragment to display, the concatenation of all of theses forms
   * the overall signature help displayed. */
  text: String,
  /** The documentation displayed when this argument is active. Used only
   * when `isArgument` is true. */
  documentation: Option[String]
)
