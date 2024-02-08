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
    val binExp1 = PBinExp(PIntLit(1)(p), PReserved.implied(PSymOp.EqEq), PIntLit(1)(p))(p)
    val binExp2 = PBinExp(PIntLit(1)(p), PReserved.implied(PSymOp.EqEq), PIntLit(1)(p))(p)
    val body = PSeqn(PDelimited.impliedBlock(Seq(PAssert(PReserved.implied(PKw.Assert), binExp1)(p), PSeqn(PDelimited.impliedBlock(Seq(PAssert(PReserved.implied(PKw.Assert), binExp2)(p))))(p))))(p)
    val method = PMethod(Seq(), PReserved.implied(PKw.Method), PIdnDef("m")(p), PGrouped.impliedParen(PDelimited.empty), None, PDelimited.empty, PDelimited.empty, Some(body))(p)
    val program = PProgram(Nil, Seq(method))(p, Seq())
    assert(frontend.doSemanticAnalysis(program) === frontend.Succ(program))
  }

  test("Semantic analysis in AST with shared nodes") {
    val p = (NoPosition, NoPosition)
    val binExp = PBinExp(PIntLit(1)(p), PReserved.implied(PSymOp.EqEq), PIntLit(1)(p))(p)
    val body = PSeqn(PDelimited.impliedBlock(Seq(PAssert(PReserved.implied(PKw.Assert), binExp)(p), PSeqn(PDelimited.impliedBlock(Seq(PAssert(PReserved.implied(PKw.Assert), binExp)(p))))(p))))(p)
    val method = PMethod(Seq(), PReserved.implied(PKw.Method), PIdnDef("m")(p), PGrouped.impliedParen(PDelimited.empty), None, PDelimited.empty, PDelimited.empty, Some(body))(p)
    val program = PProgram(Nil, Seq(method))(p, Seq())
    assert(frontend.doSemanticAnalysis(program) === frontend.Succ(program))
  }
}
