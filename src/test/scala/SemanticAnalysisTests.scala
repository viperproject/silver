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

// Test the following Viper program, with and without shared nodes in the AST.
// method main() {
//   assert 1 == 1
//   assert 1 == 1
// }

class SemanticAnalysisTests extends FunSuite {

  val binExp1 = PBinExp(PIntLit(1), "==", PIntLit(1))
  val binExp2 = PBinExp(PIntLit(1), "==", PIntLit(1))

  private def testMethod(method: PMethod): Unit = {
    val program = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(method), Seq())

    object frontend extends SilFrontend {
      def configureVerifier(args: Seq[String]): SilFrontendConfig = ???
      def createVerifier(fullCmd: String): Verifier = ???
    }

    assert(frontend.doSemanticAnalysis(program) === frontend.Succ(program))
  }

  test("Semantic analysis in AST without shared nodes") {
    testMethod(PMethod(PIdnDef("main"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PSeqn(Seq(PAssert(binExp1), PSeqn(Seq(PAssert(binExp2))))))))))
  }

  test("Semantic analysis in AST with shared nodes") {
    testMethod(PMethod(PIdnDef("main"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PSeqn(Seq(PAssert(binExp1), PSeqn(Seq(PAssert(binExp1))))))))))
  }
}
