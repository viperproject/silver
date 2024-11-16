// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination

import viper.silver.ast._
import viper.silver.parser.ReformatPrettyPrinter.{show, showOption}
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser._

case object PDecreasesKeyword extends PKw("decreases") with PKeywordLang with PKw.AnySpec with LeftNewlineIndent
case object PIfKeyword extends PKw("if") with PKeywordLang

case object PWildcardSym extends PSym("_") with PSymbolLang

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

case class PDecreasesTuple(tuple: PDelimited[PExp, PSym.Comma], condition: Option[(PReserved[PIfKeyword.type], PExp)] = None)(val pos: (Position, Position)) extends PDecreasesClause {

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // require condition to be of type bool
    condition.foreach(c => t.checkTopTyped(c._2, Some(Bool)))
    tuple.toSeq.foreach(a => t.checkTopTyped(a, None))
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    DecreasesTuple(tuple.toSeq map t.exp, condition map (_._2) map t.exp)(t.liftPos(this))
  }

  override def reformatExp(ctx: ReformatterContext): Cont =
    show(tuple, ctx) <> condition.map((e) => space <> show(e._1, ctx) <+> show(e._2, ctx)).getOrElse(nil)
}

case class PDecreasesWildcard(wildcard: PReserved[PWildcardSym.type], condition: Option[(PReserved[PIfKeyword.type], PExp)] = None)(val pos: (Position, Position)) extends PDecreasesClause {

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // require condition to be of type bool
    condition.foreach(c => t.checkTopTyped(c._2, Some(Bool)))
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    DecreasesWildcard(condition map (_._2) map t.exp)(t.liftPos(this))
  }

  override def reformatExp(ctx: ReformatterContext): Cont = show(wildcard, ctx) <+>
    condition.map((e) => show(e._1, ctx) <+> show(e._2, ctx)).getOrElse(nil)
}

case class PDecreasesStar(star: PSym.Star)(val pos: (Position, Position)) extends PDecreasesClause {

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    DecreasesStar()(t.liftPos(this))
  }

  override def reformatExp(ctx: ReformatterContext): Cont = show(star, ctx)
}

