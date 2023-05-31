// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

/** A trait for PAst nodes which should be given semantic (dynamic) highlighting in the IDE. */
trait HasSemanticHighlights {
  def getSemanticHighlights: Seq[SemanticHighlight]
}

case class SemanticHighlight(
  pos: RangePosition,
  tokenType: TokenType.TokenType,
  tokenModifier: Seq[TokenModifier.TokenModifier] = Seq(),
) extends HasRangePositions with BelongsToFile {
  override def rangePositions: Seq[RangePosition] = Seq(pos)
  override def file = pos.file
}

/** Recommended values can be found [here](https://code.visualstudio.com/api/language-extensions/semantic-highlight-guide#standard-token-types-and-modifiers),
 * additional values (`Constant` onward) are defined in `viper-ide/package.json`. */
object TokenType extends Enumeration {
    type TokenType = Value
    val Namespace, Type, Class, Enum, Interface, Struct, TypeParameter, Parameter, Variable, Property, EnumMember, Event, Function, Method, Macro, Keyword, Modifier, Comment, String, Number, Regexp, Operator, Decorator, Constant = Value
}

/** Recommended values can be found [here](https://code.visualstudio.com/api/language-extensions/semantic-highlight-guide#standard-token-types-and-modifiers),
 * additional values (`ControlFlow` onward) are defined in `viper-ide/package.json`. */
object TokenModifier extends Enumeration {
    type TokenModifier = Value
    val Declaration, Definition, Readonly, Static, Deprecated, Abstract, Async, Modification, Documentation, DefaultLibrary, ControlFlow = Value
}
