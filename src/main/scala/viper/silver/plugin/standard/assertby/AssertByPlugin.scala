// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.assertby

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast._
import viper.silver.parser.FastParser
import viper.silver.plugin.SilverPlugin

import scala.annotation.unused

class AssertByPlugin(@unused reporter: viper.silver.reporter.Reporter,
                   @unused logger: ch.qos.logback.classic.Logger,
                   @unused config: viper.silver.frontend.SilFrontendConfig,
                   @unused fp: FastParser) extends SilverPlugin {

  /**
   * Replace assert ... by statements from the AST.
   */
  override def beforeVerify(input: Program): Program = {
    println("HEREHERE")
    val transformedMethods = input.methods.map(method => {
      var assertBysInMethod = 0
      ViperStrategy.Slim({
        case r@AssertBy(exp, None) =>
          Assert(exp)(r.pos, r.info)
        case r@AssertBy(exp, Some(by)) =>
          assertBysInMethod += 1
          val nonDetLocalVarDecl = LocalVarDecl(s"__plugin_assertBy_nondet$assertBysInMethod", Bool)(r.pos)
          Seqn(Seq(
            If(nonDetLocalVarDecl.localVar,
              Seqn(
                by.ss ++ Seq(
                Assert(exp)(r.pos, r.info),
                Inhale(BoolLit(false)(r.pos))(r.pos, Synthesized)
              ), by.scopedSeqnDeclarations)(r.pos),
              Seqn(Seq(), Seq())(r.pos))(r.pos),
            Assume(exp)(r.pos, Synthesized)
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
