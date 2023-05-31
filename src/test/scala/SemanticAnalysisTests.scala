// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.frontend._
import viper.silver.parser._
import viper.silver.verifier.Verifier
import viper.silver.ast.NoPosition

class SemanticAnalysisTests extends AnyFunSuite {

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
    val p = (NoPosition, NoPosition)
    val binExp1 = PBinExp(PIntLit(1)(p), POperatorSymbol("==")(p), PIntLit(1)(p))(p)
    val binExp2 = PBinExp(PIntLit(1)(p), POperatorSymbol("==")(p), PIntLit(1)(p))(p)
    val method = PMethod(Seq(), PKeywordLang("method")(p), PIdnDef("m")(p), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PSeqn(Seq(PAssert(PKeywordStmt("assert")(p), binExp1)(p), PSeqn(Seq(PAssert(PKeywordStmt("assert")(p), binExp2)(p)))(p)))(p)))(p)))(p)
    val program = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(method), Seq(), Seq())(p)
    assert(frontend.doSemanticAnalysis(program) === frontend.Succ(program))
  }

  test("Semantic analysis in AST with shared nodes") {
    val p = (NoPosition, NoPosition)
    val binExp = PBinExp(PIntLit(1)(p), POperatorSymbol("==")(p), PIntLit(1)(p))(p)
    val method = PMethod(Seq(), PKeywordLang("method")(p), PIdnDef("m")(p), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PSeqn(Seq(PAssert(PKeywordStmt("assert")(p), binExp)(p), PSeqn(Seq(PAssert(PKeywordStmt("assert")(p), binExp)(p)))(p)))(p)))(p)))(p)
    val program = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(method), Seq(), Seq())(p)
    assert(frontend.doSemanticAnalysis(program) === frontend.Succ(program))
  }
}
