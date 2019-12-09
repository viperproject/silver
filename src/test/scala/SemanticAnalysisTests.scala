// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver

import org.scalatest.FunSuite
import viper.silver.frontend._
import viper.silver.parser._
import viper.silver.verifier.Verifier

class SemanticAnalysisTests extends FunSuite {

  object frontend extends SilFrontend {
    def configureVerifier(args: Seq[String]): SilFrontendConfig = ???
    def createVerifier(fullCmd: String): Verifier = ???
  }

  // Test the following Viper program, with and without shared nodes in the AST.
  // method m() {
  //   assert 1 == 1
  //   assert 1 == 1
  // }

  test("Semantic analysis in AST without shared nodes") {
    val binExp1 = PBinExp(PIntLit(1), "==", PIntLit(1))
    val binExp2 = PBinExp(PIntLit(1), "==", PIntLit(1))
    val method = PMethod(PIdnDef("m"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PSeqn(Seq(PAssert(binExp1), PSeqn(Seq(PAssert(binExp2)))))))))
    val program = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(method), Seq(), Seq())
    assert(frontend.doSemanticAnalysis(program) === frontend.Succ(program))
  }

  test("Semantic analysis in AST with shared nodes") {
    val binExp = PBinExp(PIntLit(1), "==", PIntLit(1))
    val method = PMethod(PIdnDef("m"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PSeqn(Seq(PAssert(binExp), PSeqn(Seq(PAssert(binExp)))))))))
    val program = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(method), Seq(), Seq())
    assert(frontend.doSemanticAnalysis(program) === frontend.Succ(program))
  }
}
