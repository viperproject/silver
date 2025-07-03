// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.unpacking

import viper.silver.ast.{Position, Stmt}
import viper.silver.parser._

/** Keyword used to define unpack statements. */
case object PUnpackKeyword extends PKw("unpack") with PKeywordStmt

case class PUnpack(unpack: PReserved[PUnpackKeyword.type], e: PExp)(val pos: (Position, Position)) extends PExtender with PStmt {

  override def translateStmt(t: Translator): Stmt = Unpack(t.exp(e))(t.liftPos(this))
}
