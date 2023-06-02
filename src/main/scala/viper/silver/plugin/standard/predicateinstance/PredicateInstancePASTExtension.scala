// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import viper.silver.ast._
import viper.silver.parser._

import scala.collection.mutable


case class PPredicateInstance(args: Seq[PExp], idnuse: PIdnUse)(val pos: (Position, Position)) extends PExtender with PExp {

  typ = PPrimitiv("PredicateInstance")()

  // TODO: Don't know if this is correct
  private val _typeSubstitutions = new scala.collection.mutable.ArrayDeque[PTypeSubstitution]()
  final override def typeSubstitutions: mutable.ArrayDeque[PTypeSubstitution] = _typeSubstitutions
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def getSubnodes(): Seq[PNode] = args :+ idnuse

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // TODO: Don't know if this is correct
    // check that idnuse is the id of a predicate
    n.definition(member = null)(idnuse) match {
      case Some(p: PPredicate) =>
        // type checking should be the same as for PPredicateAccess nodes
        val predicateAccess = PCall(idnuse, args)(p.pos)
        predicateAccess.extfunction = p
        t.checkInternal(predicateAccess)
        None
      case _ => Some(Seq("expected predicate"))
    }
  }

  override def translateExp(t: Translator): ExtensionExp = {
    PredicateInstance(args map t.exp, idnuse.name)(t.liftPos(this))
  }
}