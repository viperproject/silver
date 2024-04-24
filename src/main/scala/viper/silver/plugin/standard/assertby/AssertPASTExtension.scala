// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.assertby

import viper.silver.ast.{Position, Stmt}
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser._
import viper.silver.ast.Seqn

/** Keyword used to define refute statements. */
case object PByKeyword extends PKw("by") with PKeywordStmt

case class PAssertBy(assert: PKw.Assert, exp: PExp, by: PReserved[PByKeyword.type], body: PSeqn)(val pos: (Position, Position)) extends PExtender with PStmt {

  override def typecheck(t: TypeChecker, n: NameAnalyser):Option[Seq[String]] = {
    t.check(exp, Bool)
    t.check(body)
    None
    // TODO: fix this
  }

  override def translateStmt(t: Translator): Stmt = AssertBy(t.exp(exp), t.stmt(body).asInstanceOf[Seqn])(t.liftPos(this))
}
