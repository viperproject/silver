// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silver.plugin.standard.arp

import viper.silver.ast.{Exp, Position}
import viper.silver.parser._

/** Keyword denoting an abstract read permission. */
case object PRdKeyword extends PKw("rd") with PKeywordConstant

/** An abstract read permission `rd`, i.e., some unknown, positive permission amount. */
case class PRdPerm(keyword: PReserved[PRdKeyword.type])(val pos: (Position, Position)) extends PExtender with PExp {
  typ = TypeHelper.Perm

  override val typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    t.checkTopTyped(this, Some(expected))
    None
  }

  override def translateExp(t: Translator): Exp = RdPerm()(t.liftPos(this))
}
