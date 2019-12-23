// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import viper.silver.ast._
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser._


case class PPredicateInstance(args: Seq[PExp], idnuse: PIdnUse) extends PExtender with PExp {

  // TODO: Don't know if this is necessary...
  val _typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)
  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstitutions
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def getSubnodes(): Seq[PNode] = args

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // TODO: Don't know if this is correct
    val predicateAccess = PPredicateAccess(args, idnuse)
    t.check(predicateAccess, PTypeSubstitution.id)
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    PredicateInstance(args map t.exp, idnuse.name)(t.liftPos(this))
  }
}