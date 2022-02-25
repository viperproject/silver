// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import fastparse._
import viper.silver.parser.FastParser.{FP, anyFormalArgList, idndef, whitespace}
import viper.silver.parser.{PAnyFormalArgDecl, PIdnDef, PIdnUse, PTypeVarDecl, ParserExtension}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}


class AdtPlugin extends SilverPlugin with ParserPluginTemplate {

  /**
    * Keyword used to define ADT's
    */
  private val AdtKeyword: String = "adt"

  /**
    * Parser for ADT declaration.
    *
    * Example of a List:
    *
    * adt List[T] {
    *   Nil()
    *   Cons(value: T, tail: List[T])
    * }
    *
    */
  def adtDecl[_: P]: P[PAdt] = FP(AdtKeyword ~/ idndef ~ ("[" ~ adtTypeVarDecl.rep(sep = ",") ~ "]").? ~ "{" ~ adtConstructorDecl.rep ~
    "}").map {
    case (pos, (name, typparams, constructors)) =>
      PAdt(
        name,
        typparams.getOrElse(Nil),
        constructors map (c => PAdtConstructor(c.idndef, c.formalArgs)(PIdnUse(name.name)(name.pos))(c.pos)))(pos)
  }

  def adtTypeVarDecl[_: P]: P[PTypeVarDecl] = FP(idndef).map{ case (pos, i) => PTypeVarDecl(i)(pos) }

  def adtConstructorDecl[_: P]: P[PAdtConstructor1] = FP(adtConstructorSignature ~ ";".?).map {
    case (pos, cdecl) => cdecl match {
      case (name, formalArgs) => PAdtConstructor1(name, formalArgs)(pos)
    }
  }

  def adtConstructorSignature[_: P]: P[(PIdnDef, Seq[PAnyFormalArgDecl])] = P(idndef ~ "(" ~ anyFormalArgList ~ ")")

  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String](AdtKeyword))
    // Add new declaration
    ParserExtension.addNewDeclAtEnd(adtDecl(_))
    // TODO: Add custom parsers
    input
  }

}

