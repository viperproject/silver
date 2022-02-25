// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import viper.silver.ast.{AnyLocalVarDecl, Declaration, ErrorTrafo, ExtensionMember, Info, LocalVarDecl, NoInfo, NoPosition, NoTrafos, Node, Position, TypeVar}

/**
  * This class represents a user-defined ADT.
  *
  * @param name name of the ADT
  * @param constructors sequence of corresponding constructors
  * @param typVars sequence of type variables (generics)
  */
case class Adt(name: String, constructors: Seq[AdtConstructor], typVars: Seq[TypeVar] = Nil)
                 (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionMember {
  val scopedDecls: Seq[Declaration] = Seq()

  override def extensionSubnodes: Seq[Node] = constructors ++ typVars
}

/**
  * This class represents an ADT constructor
  *
  * @param name name of the ADT constructor
  * @param formalArgs sequence of arguments of the constructor
  * @param adtName the name corresponding of the corresponding ADT
  */
case class AdtConstructor(name: String, formalArgs: Seq[AnyLocalVarDecl])
                     (val pos: Position = NoPosition, val info: Info = NoInfo, val adtName : String, val errT: ErrorTrafo = NoTrafos)
  extends ExtensionMember {

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
  val scopedDecls: Seq[Declaration] = formalArgs.filter(p => p.isInstanceOf[LocalVarDecl]).asInstanceOf[Seq[LocalVarDecl]]

  override def extensionSubnodes: Seq[Node] = formalArgs
}


