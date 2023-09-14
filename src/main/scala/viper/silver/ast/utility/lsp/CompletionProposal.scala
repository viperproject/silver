// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

trait HasSuggestionScopeRanges {
  def getSuggestionScopeRanges: Seq[SuggestionScopeRange]
}

case class SuggestionScopeRange(
  range: RangePosition,
  scope: SuggestionScope,
) extends HasRangePositions with SelectableInBound {
  override val bound: SelectionBoundTrait = SelectionBoundScope(range)
  override def rangePositions: Seq[RangePosition] = Seq(range)
}

trait HasCompletionProposals {
  def getCompletionProposals: Seq[CompletionProposal]
}

case class CompletionProposal(
  label: String,
  /** Determines the icon which appears next to the label */
  kind: CompletionKind.CompletionKind,
  /** Extra detail to show alongside the label (e.g. type) */
  detail: Option[String] = None,
  /** Extra description to show right aligned in the same row as the label */
  description: Option[String] = None,
  /** The new text that will be inserted when selected. If none, `label` is used. */
  newText: Option[String] = None,
  /** If the `newText` is inserted as a plain string or as a snippet.
   * See https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#snippet_syntax
  */
  insertTextFormat: InsertTextFormat.InsertTextFormat,
  /** Items are always first grouped by the SuggestionScope and these groups are sorted by
   * the size of their corresponding scope (items from the more specific groups are shown first).
   * Then within these groups items are first sorted by `sortPriority` and then alphabetically by 
   * the `label`.
  */
  // sortPriority: Byte = 0,
  /** Determines how the label appears (e.g. strikethrough) */
  tags: Seq[SymbolTag.SymbolTag] = Seq(),
  documentationTitle: Option[String] = None,
  /** A human-readable string that represents a doc-comment. */
  documentation: Option[String] = None,
  suggestionBound: SuggestionBound,
) extends HasRangePositions with SuggestableInBound {
  override def rangePositions: Seq[RangePosition] = suggestionBound.rangePositions
}

object InsertTextFormat extends Enumeration(1) {
    type InsertTextFormat = Value
    val PlainText, Snippet = Value
}

object CompletionKind extends Enumeration(1) {
    type CompletionKind = Value
    val Text, Method, Function, Constructor, Field, Variable, Class, Interface, Module, Property, Unit, Value_, Enum, Keyword, Snippet, Color, File, Reference, Folder, EnumMember, Constant, Struct, Event, Operator, TypeParameter = Value
}

trait SuggestionScope {
  def isSubtype(sup: SuggestionScope): Boolean = this == sup
}
case object MemberScope extends SuggestionScope
case object CallableSignatureScope extends SuggestionScope
case object DomainScope extends SuggestionScope

case object StatementScope extends SuggestionScope
case object ExpressionScope extends SuggestionScope
case object LabelScope extends SuggestionScope
case object TypeScope extends SuggestionScope

case class SuggestionBound(
  range: Option[RangePosition],
  /** The type of scope within which this suggestion can appear. */
  scope: Map[SuggestionScope, Byte],
  /** If one of the characters in this list appears **before** the identifier being
   * typed. The this will be shown, regardless of the scope above.
   * For field names this is `Seq('.')`, for types this is `Seq(':')`.
  */
  starting: Option[Map[Char, Byte]],
  // /** Is the suggestion scope above strict? If true the suggestion will only
  //  * appear within the given scope type, otherwise it will appear in all scopes
  //  * but will be ranked lower. This is useful for smaller scopes which are not
  //  * always very precise or are parsed only after writing is complete. For example,
  //  * the `Expression` scope after an `assert` is not immediately visible since we
  //  * get a parse error when there is nothing after an `assert`.
  // */
  // strictScope: Boolean,
) extends SelectableInBound with HasRangePositions {
  override val bound: SelectionBoundTrait = range.map(SelectionBoundScope(_)).getOrElse(SelectionBound)
  override def rangePositions: Seq[RangePosition] = range.toSeq
}
