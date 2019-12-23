// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, show, space, ssep, text}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.{ConsistencyError, VerificationResult}

/*
case object PredicateInstanceTypeTest extends ExtensionType {
  override def substitute(typVarsMap: Map[TypeVar, Type]): Type = typVarsMap.getOrElse(this.typeVariables.head, this)
  override def isConcrete: Boolean = true

  override def isSubtype(other: Type): Boolean = {
    other match {
      case DomainType("PredicateInstance", _) => true
      case d => d.isSubtype(DomainType("PredicateInstance", Map[viper.silver.ast.TypeVar,viper.silver.ast.Type]())(Nil))
    }
  }

  override def isSubtype(other: Typed): Boolean = {
    isSubtype(other.typ)
  }
}
*/

case class PredicateInstance(args: Seq[Exp], p: String)(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = args

  override def typ: Type = PredicateInstance.getType

  override def verifyExtExp(): VerificationResult = ???

  override def prettyPrint: PrettyPrintPrimitives#Cont =
    text("@") <> text(p) <> parens(ssep(args map show, char (',') <> space))

  // TODO:
  override lazy val check: Seq[ConsistencyError] = Nil
}

object PredicateInstance {
  val PredicateInstanceDomainName = "PredicateInstance"
  def getType = DomainType(PredicateInstanceDomainName, Map[viper.silver.ast.TypeVar,viper.silver.ast.Type]())(Nil)
}