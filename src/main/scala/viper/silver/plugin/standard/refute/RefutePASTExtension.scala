// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.refute

import viper.silver.ast.{Position, Stmt}
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser._

/** Keyword used to define refute statements. */
case object PRefuteKeyword extends PKw("refute") with PKeywordStmt

case class PRefute(refute: PReserved[PRefuteKeyword.type], e: PExp)(val pos: (Position, Position)) extends PExtender with PStmt {

  override def typecheck(t: TypeChecker, n: NameAnalyser):Option[Seq[String]] = {
    t.check(e, Bool)
    None
  }

  override def translateStmt(t: Translator): Stmt = Refute(t.exp(e))(t.liftPos(this))
}
