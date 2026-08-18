// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.


package viper.silver.plugin.sif

import fastparse._
import viper.silver.ast.Program
import viper.silver.parser.{FastParser, PKeywordLang, PKw}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

import scala.annotation.unused

case object PLowKeyword extends PKw("low") with PKeywordLang
case object PLowEventKeyword extends PKw("lowEvent") with PKeywordLang
case object PRelKeyword extends PKw("rel") with PKeywordLang


class SIFPlugin(@unused reporter: viper.silver.reporter.Reporter,
                @unused logger: ch.qos.logback.classic.Logger,
                @unused config: viper.silver.frontend.SilFrontendConfig,
                fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{exp, integer, ParserExtension, lineCol, _file}
  import viper.silver.parser.FastParserCompanion.{PositionParsing, reservedKw, whitespace}

  def low[$: P]: P[PLowExp] = P(P(PLowKeyword) ~ "(" ~ exp ~ ")").map { case (_, e) => PLowExp(e)(_) }.pos
  def rel[$: P]: P[PRelExp] = P(P(PRelKeyword) ~ "(" ~ exp ~ "," ~ integer ~ ")").map { case (_, e, i) => PRelExp(e, i)(_) }.pos
  def lowEvent[$: P]: P[PLowEventExp] = P(P(PLowEventKeyword)).map { case (_) => PLowEventExp()(_) }.pos

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewKeywords(Set(PLowKeyword, PLowEventKeyword, PRelKeyword))
    ParserExtension.addNewExpAtEnd(low(_))
    ParserExtension.addNewExpAtEnd(rel(_))
    ParserExtension.addNewExpAtEnd(lowEvent(_))
    input
  }

  override def beforeVerify(input: Program): Program = {
    SIFExtendedTransformer.Config.reportError = this.reportError
    SIFExtendedTransformer.transform(input, false)
  }
}
