// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver

package object reporter {
  type Time = Long  // in milliseconds
  type File = java.nio.file.Path

  type Entity = viper.silver.ast.Member with Serializable
  def print(e: Entity): String =  // FIXME: treat the natural delimiters and insert `;` where needed.
    e.toString().replaceAll("""\n""", " ").replaceAll("""\s+""", " ")

  type DefPosition = viper.silver.ast.Position
  type DefScope = viper.silver.ast.AbstractSourcePosition
  type ViperType = viper.silver.ast.Type

  sealed trait SymbolKind {
    val name: String
  }

  sealed trait TypedSymbol extends SymbolKind {
    val viperType: ViperType
  }

  // The following case classes are essentially named tuple wrappers.
  case object ViperDomain extends SymbolKind {
    val name = "Domain"
  }

  case object ViperAxiom extends SymbolKind {
    val name = "Axiom"
  }

  case object ViperFunction extends SymbolKind {
    val name = "Function"
  }

  case object ViperPredicate extends SymbolKind {
    val name = "Predicate"
  }

  case class ViperField(viperType: ViperType) extends TypedSymbol {
    val name = "Field"
  }

  case object ViperMethod extends SymbolKind {
    val name = "Method"
  }

  case class ViperArgument(viperType: ViperType) extends TypedSymbol {
    val name = "Argument"
  }

  case class ViperReturnParameter(viperType: ViperType) extends TypedSymbol {
    val name = "Return"
  }

  case object ViperUntypedLocalDefinition extends SymbolKind {
    // e.g. a label
    val name = "Local"
  }

  case class ViperTypedLocalDefinition(viperType: ViperType) extends TypedSymbol {
    // e.g. var x:Int
    val name = "Local"
  }

  // TODO: discuss if "Declaration" is a better term than e.g. "Definition"
  case class Definition(name: String, typ: SymbolKind, location: DefPosition,
                        scope: Option[DefScope] = None)

  case class Import(file: File, from: Option[DefScope])
}
