// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import viper.silver.ast.{Member, Position}
import viper.silver.parser.{NameAnalyser, PAnyFormalArgDecl, PExtender, PGlobalDeclaration, PIdnDef, PIdnUse, PMember, PNode, PTypeVarDecl, Translator, TypeChecker}


case class PAdt(idndef: PIdnDef, typVars: Seq[PTypeVarDecl], constructors: Seq[PAdtConstructor])(val pos: (Position, Position)) extends PExtender with PMember with PGlobalDeclaration {

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ typVars ++ constructors

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }

  // TODO: Implement
  override def translateMemberSignature(t: Translator): Member = ???

  // TODO: Implement
  override def translateMember(t: Translator): Member = ???
}

case class PAdtConstructor(idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl])(val adtName: PIdnUse)(val pos: (Position, Position)) extends PExtender with PMember with PGlobalDeclaration {

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }

  // TODO: Implement
  override def translateMemberSignature(t: Translator): Member = ???

  // TODO: Implement
  override def translateMember(t: Translator): Member = ???

}

case class PAdtConstructor1(idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl])(val pos: (Position, Position))
