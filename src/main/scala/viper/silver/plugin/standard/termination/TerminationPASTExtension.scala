// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination

import viper.silver.ast._
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser._

/**
 * Any possible decreases clause extends from this trait.
 */
sealed trait PDecreasesClause extends PExtender with PExp {

  typ = TypeHelper.Bool

  // TODO: Don't know if this is necessary...
  val _typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstitutions

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}
}

case class PDecreasesTuple(tuple: Seq[PExp], condition: Option[PExp] = None) extends PDecreasesClause {

  override val getSubnodes: Seq[PNode] = tuple ++ condition

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // require condition to be of type bool
    condition.foreach(c => t.checkTopTyped(c, Some(Bool)))
    tuple.foreach(a => t.checkTopTyped(a, None))
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    DecreasesTuple(tuple map t.exp, condition map t.exp)(t.liftPos(this))
  }
}

case class PDecreasesWildcard(condition: Option[PExp] = None) extends PDecreasesClause {

  override val getSubnodes: Seq[PNode] = condition.toSeq

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // require condition to be of type bool
    condition.foreach(c => t.checkTopTyped(c, Some(Bool)))
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    DecreasesWildcard(condition map t.exp)(t.liftPos(this))
  }
}

case class PDecreasesStar() extends PDecreasesClause {
  override val getSubnodes: Seq[PNode] = Nil

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    DecreasesStar()(t.liftPos(this))
  }
}

