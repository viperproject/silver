// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast.FilePosition

/** A trait for PAst nodes which should be given semantic (dynamic) highlighting
 * in the IDE. Useful for extension nodes. */
trait HasSemanticTokens {
  def semanticTokens: Seq[SemanticHighlight]
}

case class SemanticHighlight(
  start: FilePosition,
  end: FilePosition,
  tokenType: TokenType.TokenType,
  /** Does not seem to have much effect */
  tokenHighlight: Seq[TokenModifier.TokenModifier] = Seq(),
)

/** Recommended values can be found [here](https://code.visualstudio.com/api/language-extensions/semantic-highlight-guide#standard-token-types-and-modifiers) */
object TokenType extends Enumeration {
    type TokenType = Value
    val Namespace, Type, Class, Enum, Interface, Struct, TypeParameter, Parameter, Variable, Property, EnumMember, Event, Function, Method, Macro, Keyword, Modifier, Comment, String, Number, Regexp, Operator, Decorator = Value
}

object TokenModifier extends Enumeration {
    type TokenModifier = Value
    val Declaration, Definition, Readonly, Static, Deprecated, Abstract, Async, Modification, Documentation, DefaultLibrary = Value
}
