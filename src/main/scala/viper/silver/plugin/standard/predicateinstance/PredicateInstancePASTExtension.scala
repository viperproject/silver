// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import viper.silver.ast._
import viper.silver.ast.utility.lsp.BuiltinFeature
import viper.silver.parser._

import scala.collection.mutable

case object PPredicateInstanceKeyword extends PKw("PredicateInstance", TODOPredicateInstanceDoc) with PKeywordType
case object TODOPredicateInstanceDoc extends BuiltinFeature(
  """TODO""".stripMargin.replaceAll("\n", " ")
)
/**
 * Syntactic marker for predicate instances
 */
case object PMarkerSymbol extends PSym("#") with PSymbolLang

case class PPredicateInstance(m: PReserved[PMarkerSymbol.type], idnuse: PIdnRef, args: PDelimited.Comma[PSym.Paren, PExp])(val pos: (Position, Position)) extends PExtender with PExp {

  typ = PPrimitiv(PReserved(PPredicateInstanceKeyword)(NoPosition, NoPosition))(NoPosition, NoPosition)

  // TODO: Don't know if this is correct
  private val _typeSubstitutions = new scala.collection.mutable.ArrayDeque[PTypeSubstitution]()
  final override def typeSubstitutions: mutable.ArrayDeque[PTypeSubstitution] = _typeSubstitutions
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def getSubnodes(): Seq[PNode] = Seq(m, idnuse, args)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // TODO: Don't know if this is correct
    // check that idnuse is the id of a predicate
    n.definition(member = null)(idnuse) match {
      case Some(p: PPredicate) =>
        // type checking should be the same as for PPredicateAccess nodes
        val predicateAccess = PCall(idnuse, args, None)(p.pos)
        predicateAccess.funcDecl = Some(p)
        t.checkInternal(predicateAccess)
        None
      case _ => Some(Seq("expected predicate"))
    }
  }

  override def translateExp(t: Translator): ExtensionExp = {
    PredicateInstance(idnuse.name, args.inner.toSeq map t.exp)(t.liftPos(this))
  }
}
