// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.refute

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives

/** An `FailureExpectedInfo` info that tells us that this assert is a refute. */
case class RefuteInfo(refute: Refute) extends FailureExpectedInfo

case class Refute(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = text("refute") <+> toParenDoc(exp)

  override val extensionSubnodes: Seq[Node] = Seq(exp)
}
