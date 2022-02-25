// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import viper.silver.ast.{Member, NoInfo, Position, TypeVar}
import viper.silver.parser.{NameAnalyser, PAnyFormalArgDecl, PExtender, PGlobalDeclaration, PIdentifier, PIdnDef, PIdnUse, PMember, PNode, PTypeVarDecl, Translator, TypeChecker}
import viper.silver.plugin.standard.adt.PAdtConstructor.findAdtConstructor


case class PAdt(idndef: PIdnDef, typVars: Seq[PTypeVarDecl], constructors: Seq[PAdtConstructor])(val pos: (Position, Position)) extends PExtender with PMember with PGlobalDeclaration {

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ typVars ++ constructors

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // TODO: Implement type checking
    None
  }

  override def translateMemberSignature(t: Translator): Adt = {
    Adt(idndef.name, null, typVars map (t => TypeVar(t.idndef.name)))(t.liftPos(this))
  }

  override def translateMember(t: Translator): Member = {
    val a = PAdt.findAdt(idndef, t)
    val aa = a.copy(constructors = constructors map (c => PAdtConstructor.findAdtConstructor(c.idndef, t)))(a.pos, a.info, a.errT)
    t.getMembers()(a.name) = aa
    aa
  }

}

object PAdt {
  /**
    * This is a helper method helper that can be called if one knows which 'id' refers to an ADT
    *
    * @param id identifier of the ADT
    * @param t translator unit
    * @return the corresponding ADT object
    */
  def findAdt(id: PIdentifier, t: Translator): Adt = t.getMembers()(id.name).asInstanceOf[Adt]

}

case class PAdtConstructor(idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl])(val adtName: PIdnUse)(val pos: (Position, Position)) extends PExtender with PMember with PGlobalDeclaration {

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // TODO: Implement type checking
    None
  }

  override def translateMemberSignature(t: Translator): AdtConstructor = {
    AdtConstructor(idndef.name, formalArgs map t.liftAnyVarDecl)(t.liftPos(this), NoInfo, adtName.name)
  }

  override def translateMember(t: Translator): Member = {
    findAdtConstructor(idndef, t)
  }
}

object PAdtConstructor {
  /**
    * This is a helper method helper that can be called if one knows which 'id' refers to an ADTConstructor
    *
    * @param id identifier of the ADT constructor
    * @param t  translator unit
    * @return the corresponding ADTConstructor object
    */
  def findAdtConstructor(id: PIdentifier, t: Translator): AdtConstructor = t.getMembers()(id.name).asInstanceOf[AdtConstructor]
}

case class PAdtConstructor1(idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl])(val pos: (Position, Position))
