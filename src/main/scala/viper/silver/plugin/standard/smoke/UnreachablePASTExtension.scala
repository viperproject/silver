// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.smoke

import viper.silver.ast.{Position, Stmt}
import viper.silver.parser._

/** Keyword used to define `unreachable` statement. */
case object PUnreachableKeyword extends PKw("unreachable") with PKeywordStmt

case class PUnreachable(kw: PReserved[PUnreachableKeyword.type])(val pos: (Position, Position)) extends PExtender with PStmt {
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }

  override def translateStmt(t: Translator): Stmt = Unreachable()(t.liftPos(this))
}
