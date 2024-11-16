// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import viper.silver.ast._
import viper.silver.parser.ReformatPrettyPrinter.show
import viper.silver.parser._

import scala.collection.mutable

case object PPredicateInstanceKeyword extends PKw("PredicateInstance") with PKeywordType

/**
 * Syntactic marker for predicate instances
 */
case object PMarkerSymbol extends PSym("#") with PSymbolLang

case class PPredicateInstance(m: PReserved[PMarkerSymbol.type], idnuse: PIdnRef[PPredicate], args: PDelimited.Comma[PSym.Paren, PExp])(val pos: (Position, Position)) extends PExtender with PExp {

  typ = PPrimitiv(PReserved(PPredicateInstanceKeyword)(NoPosition, NoPosition))(NoPosition, NoPosition)

  // TODO: Don't know if this is correct
  private val _typeSubstitutions = new scala.collection.mutable.ArrayDeque[PTypeSubstitution]()
  final override def typeSubstitutions: mutable.ArrayDeque[PTypeSubstitution] = _typeSubstitutions
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    if (idnuse.decls.isEmpty)
      Some(Seq(s"undefined predicate instance `${idnuse.name}`"))
    if (idnuse.decls.size > 1)
      Some(Seq(s"ambiguous predicate instance `${idnuse.name}`"))
    else {
      // type checking should be the same as for PPredicateAccess nodes
      val predicateAccess = PCall(idnuse.retype(), args, None)(pos)
      t.checkInternal(predicateAccess)
      None
    }
  }

  override def translateExp(t: Translator): ExtensionExp = {
    PredicateInstance(idnuse.name, args.inner.toSeq map t.exp)(t.liftPos(this))
  }

  override def reformatExp(ctx: ReformatterContext): Cont = show(m, ctx) <>
    show(idnuse, ctx) <> show(args, ctx)
}
