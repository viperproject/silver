// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination

import viper.silver.ast._
import viper.silver.ast.utility.lsp.BuiltinFeature
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser._

case object PDecreasesKeyword extends PKw("decreases", TODODecreasesDoc) with PKeywordLang with PSpecification
case object PIfKeyword extends PKw("if", TODODecreasesDoc) with PKeywordLang
case object TODODecreasesDoc extends BuiltinFeature(
  """TODO""".stripMargin.replaceAll("\n", " ")
)

case object PStarSymbol extends PSym("*") with PSymbolLang

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

case class PDecreasesTuple(tuple: Seq[PExp], condition: Option[(PReserved[PIfKeyword.type], PExp)] = None)(val pos: (Position, Position)) extends PDecreasesClause {

  override val getSubnodes: Seq[PNode] = tuple ++ condition.toSeq.flatMap(c => Seq(c._1, c._2))

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // require condition to be of type bool
    condition.foreach(c => t.checkTopTyped(c._2, Some(Bool)))
    tuple.foreach(a => t.checkTopTyped(a, None))
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    DecreasesTuple(tuple map t.exp, condition map (_._2) map t.exp)(t.liftPos(this))
  }

  override def prettyNoBrackets: String = tuple.map(_.pretty).mkString(", ") + condition.map(c => s" ${c._1.pretty} ${c._2.pretty}").getOrElse("")
}

case class PDecreasesWildcard(condition: Option[(PReserved[PIfKeyword.type], PExp)] = None)(val pos: (Position, Position)) extends PDecreasesClause {

  override val getSubnodes: Seq[PNode] = condition.toSeq.flatMap(c => Seq(c._1, c._2))

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    // require condition to be of type bool
    condition.foreach(c => t.checkTopTyped(c._2, Some(Bool)))
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    DecreasesWildcard(condition map (_._2) map t.exp)(t.liftPos(this))
  }

  override def prettyNoBrackets: String = "_" + condition.map(c => s" ${c._1.pretty} ${c._2.pretty}").getOrElse("")
}

case class PDecreasesStar(star: PReserved[PStarSymbol.type])(val pos: (Position, Position)) extends PDecreasesClause {
  override val getSubnodes: Seq[PNode] = Seq(star)

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    DecreasesStar()(t.liftPos(this))
  }

  override def prettyNoBrackets: String = star.pretty
}

