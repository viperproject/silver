// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.assertby

import fastparse._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast._
import viper.silver.parser.FastParserCompanion
import viper.silver.parser.FastParser
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

import scala.annotation.unused
import viper.silver.parser.PKw

class AssertByPlugin(@unused reporter: viper.silver.reporter.Reporter,
                   @unused logger: ch.qos.logback.classic.Logger,
                   @unused config: viper.silver.frontend.SilFrontendConfig,
                   fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{stmtBlock, exp, ParserExtension, lineCol, _file}
  import FastParserCompanion.{PositionParsing, reservedKw, whitespace}

  /** Parser for assertBy statements. */
  def assertBy[$: P]: P[PAssertBy] = P((P(PKw.Assert) ~ exp ~ P(PByKeyword) ~ stmtBlock()) map (PAssertBy.apply _).tupled).pos

  /** Add assertBy to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set(PByKeyword))
    // Add new parser to the precondition
    ParserExtension.addNewStmtAtEnd(assertBy(_))
    input
  }

  /**
   * Remove assertBy statements from the AST and add them as non-det asserts.
   */
  override def beforeVerify(input: Program): Program = {
    val transformedMethods = input.methods.map(method => {
      var assertBysInMethod = 0
      ViperStrategy.Slim({
        case r@AssertBy(exp, by) =>
          assertBysInMethod += 1
          val nonDetLocalVarDecl = LocalVarDecl(s"__plugin_assertBy_nondet$assertBysInMethod", Bool)(r.pos)
          Seqn(Seq(
            If(nonDetLocalVarDecl.localVar,
              Seqn(
                by.ss ++ Seq(
                Assert(exp)(r.pos, r.info),
                Inhale(BoolLit(false)(r.pos))(r.pos, Synthesized)
              ), by.scopedSeqnDeclarations)(r.pos),
              Seqn(Seq(), Seq())(r.pos))(r.pos)
          ),
            Seq(nonDetLocalVarDecl)
          )(r.pos)
      }).recurseFunc({
        case method: Method => Seq(method.body)
      }).execute[Method](method)
    })
    Program(input.domains, input.fields, input.functions, input.predicates, transformedMethods, input.extensions)(input.pos, input.info, input.errT)
  }
}
