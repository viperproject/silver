// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.VerificationResult

/**
  * Expression used to define the (possible) decreases clause (termination measure)
  */
sealed trait DecreasesExp extends ExtensionExp with Node

/**
  * Expression representing the decreases clause (termination measure).
  * @param extensionSubnodes Seq of expressions defining the termination measure (lex order)
  */
case class DecreasesTuple(extensionSubnodes: Seq[Exp] = Nil)(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends DecreasesExp {
  override def verifyExtExp(): VerificationResult = ???
  override val extensionIsPure = true

  override val typ: Type = Bool

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = text("decreases") <> parens(ssep(extensionSubnodes map (toParenDoc(_)), char(',') <> space))
}

/**
  * Expression representing the decreases star option (possibly non terminating).
  * No termination checks are done.
  */
case class DecreasesStar()(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends DecreasesExp{
  override def verifyExtExp(): VerificationResult = ???
  override val extensionIsPure: Boolean = true

  override val extensionSubnodes: Seq[Node] = Nil

  override val typ: Type = Bool

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = text("decreasesStar")

}
