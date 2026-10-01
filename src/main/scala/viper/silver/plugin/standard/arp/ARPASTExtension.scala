// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silver.plugin.standard.arp

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.text
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.VerificationResult

/** An abstract read permission `rd`. It is encoded away by the [[ARPPlugin]] before verification. */
case class RdPerm()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Seq()

  override def typ: Type = Perm

  override def verifyExtExp(): VerificationResult = ???

  override def prettyPrint: PrettyPrintPrimitives#Cont = text("rd")
}
