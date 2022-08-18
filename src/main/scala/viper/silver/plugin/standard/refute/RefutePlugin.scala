// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.refute

import fastparse.P
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast._
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser.{FastParser, ParserExtension}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier._
import viper.silver.verifier.errors.AssertFailed

class RefutePlugin(reporter: viper.silver.reporter.Reporter,
                   logger: ch.qos.logback.classic.Logger,
                   config: viper.silver.frontend.SilFrontendConfig,
                   fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{FP, keyword, exp}

  /** Keyword used to define refute statements. */
  private val refuteKeyword: String = "refute"

  private var refuteAsserts: Map[Position, Refute] = Map()

  /** Parser for refute statements. */
  def refute[_: P]: P[PRefute] =
    FP(keyword(refuteKeyword) ~/ exp).map{ case (pos, e) => PRefute(e)(pos) }

  /** Add refute to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String](refuteKeyword))
    // Add new parser to the precondition
    ParserExtension.addNewStmtAtEnd(refute(_))
    input
  }

  /**
   * Remove refute statements from the AST and add them as non-det asserts.
   * The ⭐ is nice since such a variable name cannot be parsed, but will it cause issues?
   */
  override def beforeVerify(input: Program): Program =
    ViperStrategy.Slim({
      case r@Refute(exp) => {
        this.refuteAsserts += (r.pos -> r)
        Seqn(Seq(
          If(LocalVar(s"__plugin_refute_nondet${this.refuteAsserts.size}", Bool)(r.pos),
            Seqn(Seq(
              Assert(exp)(r.pos, RefuteInfo),
              Inhale(BoolLit(false)(r.pos))(r.pos)
            ), Seq())(r.pos),
            Seqn(Seq(), Seq())(r.pos))(r.pos)
          ),
          Seq(LocalVarDecl(s"__plugin_refute_nondet${this.refuteAsserts.size}", Bool)(r.pos))
        )(r.pos)
      }
    }).recurseFunc({
      case Method(_, _, _, _, _, body) => Seq(body)
    }).execute(input)

  /** Remove refutation related errors and add refuteAsserts that didn't report an error. */
  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    val errors: Seq[AbstractError] = (input match {
      case Success => Seq()
      case Failure(errors) => {
        errors.filter {
          case AssertFailed(a, _, _) if a.info == RefuteInfo => {
            this.refuteAsserts -= a.pos
            false
          }
          case _ => true
        }
      }
    }) ++ this.refuteAsserts.map(r => RefuteFailed(r._2, RefutationTrue(r._2.exp)))
    if (errors.length == 0) Success
    else Failure(errors)
  }
}
