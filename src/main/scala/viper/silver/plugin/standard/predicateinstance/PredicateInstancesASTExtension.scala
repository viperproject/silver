// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, space, ssep, text, show}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.{ConsistencyError, VerificationResult}

case object PredicateInstanceType extends ExtensionType {

  override def substitute(typVarsMap: Map[TypeVar, Type]): Type = typVarsMap.getOrElse(this.typeVariables.head, this)
  override def isConcrete: Boolean = true
}


case class PredicateInstance(args: Seq[Exp], p: String)(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = args

  override def typ: Type = PredicateInstanceType

  override def verifyExtExp(): VerificationResult = ???

  override def prettyPrint: PrettyPrintPrimitives#Cont =
    text("@") <> text(p) <> parens(ssep(args map show, char (',') <> space))

  lazy val predicateAccessPredicate: PredicateAccessPredicate = PredicateAccessPredicate(PredicateAccess(args, p)(), EpsilonPerm()())()
}

case class NestedPredicates(p1: Exp, p2: Exp)
                           (override val pos: Position = NoPosition,
                            override val info: Info = NoInfo,
                            override val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def typ: Type = Bool

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Seq(p1, p2)

  override def verifyExtExp(): VerificationResult = ???

  override lazy val check: Seq[ConsistencyError] = Nil ++
    (if (p1.typ.isSubtype(PredicateInstanceType)) {None}
    else {Some(ConsistencyError("Expected Predicate Instance Type. But is " + p1.typ, p1.pos))}) ++
    (if (p2.typ.isSubtype(PredicateInstanceType)) {None}
    else {Some(ConsistencyError("Expected Predicate Instance Type. But is " + p2.typ, p2.pos))})

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("NestedPredicate") <> parens(ssep(Seq(p1, p2) map show, char (',') <> space))
}