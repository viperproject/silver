// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver

import viper.silver.ast.Type

package object reporter {
  type Time = Long  // in milliseconds
  type File = java.nio.file.Path

  type Entity = viper.silver.ast.Member with Serializable
  def print(e: Entity): String =  // FIXME: treat the natural delimiters and insert `;` where needed.
    e.toString().replaceAll("""\n""", " ").replaceAll("""\s+""", " ")
  
  type Position = viper.silver.ast.SourcePosition
  type Scope = viper.silver.ast.AbstractSourcePosition

  trait SymbolType {
    val name: String
  }

  trait TypedSymbol extends SymbolType {
    val viperType: Type
  }

  // The following case classes are essentially named tuple wrappers.
  case object ViperDomain extends SymbolType {
    val name = "Domain"
  }

  case object ViperAxiom extends SymbolType {
    val name = "Axiom"
  }

  case object ViperFunction extends SymbolType {
    val name = "Function"
  }

  case object ViperPredicate extends SymbolType {
    val name = "Predicate"
  }

  case class ViperField(viperType: Type) extends TypedSymbol {
    val name = "Field"
  }

  case object ViperMethod extends SymbolType {
    val name = "Method"
  }

  case class ViperArgument(viperType: Type) extends TypedSymbol {
    val name = "Argument"
  }

  case class ViperReturnParameter(viperType: Type) extends TypedSymbol {
    val name = "Return"
  }

  case object ViperUntypedLocalDefinition extends SymbolType {
    val name = "Local"
  }

  case class ViperTypedLocalDefinition(viperType: Type) extends TypedSymbol {
    val name = "Local"
  }

  case class Definition(name: String, typ: SymbolType, location: Position,
                        scope: Option[Scope] = None)
}
