// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

import java.nio.file.Path

trait HasDocumentSymbol {
  def getSymbolChildren: Seq[DocumentSymbol]
  def getSymbol: Option[DocumentSymbol]
}

case class DocumentSymbol(
  /** The name to show for the symbol */
  name: String,
  /** Extra detail to show alongside symbol (e.g. type) */
  detail: Option[String] = None,
  /** The range enclosing this symbol (e.g. a function signature and body) */
  range: RangePosition,
  /** The range which should be selected when this symbol is picked (e.g. the name of a function) */
  selectionRange: RangePosition,
  /** Determines the icon which appears next to a symbol */
  kind: SymbolKind.SymbolKind,
  /** Determines how the symbol appears (e.g. strikethrough) */
  tags: Seq[SymbolTag.SymbolTag] = Seq(),
  /** Does it import a file? Setting this will cause all of the symbols from
   * the imported file to be displayed as children of this symbol. One must ensure
   * that there is no circular dependency! */
  imports: Option[Path] = None,
  /** What are the sub-symbols */
  var children: Seq[DocumentSymbol] = Seq(),
) extends HasRangePositions with BelongsToFile {
  require(range.file == selectionRange.file, "Range and selection range must be in the same file")
  require(range.start <= selectionRange.start && selectionRange._end <= range._end, "Selection range must be within range")

  override def rangePositions: Seq[RangePosition] = Seq(range, selectionRange) ++ children.flatMap(_.rangePositions)
  override def file = range.file
}

object SymbolKind extends Enumeration(1) {
    type SymbolKind = Value
    val File, Module, Namespace, Package, Class, Method, Property, Field, Constructor, Enum, Interface, Function, Variable, Constant, String, Number, Boolean, Array, Object, Key, Null, EnumMember, Struct, Event, Operator, TypeParameter = Value
}
object SymbolTag extends Enumeration(1) {
    type SymbolTag = Value
    val Deprecated = Value
}
