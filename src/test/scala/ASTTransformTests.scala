// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver

import org.scalatest.FunSuite
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.frontend._
import viper.silver.verifier.Verifier

class ASTTransformTests extends FunSuite {
  object frontend extends SilFrontend {
    def configureVerifier(args: Seq[String]): SilFrontendConfig = ???
    def createVerifier(fullCmd: String): Verifier = ???
  }

  test("Rewriting nodes and updating context during AST traversal") {
    // Thansforms this code:
    // method m()
    // {
    //   assert 1 == 1
    // }
    //
    // Into this program:
    // method m()
    // {
    //   assert 3 == 4
    // }

    import viper.silver.parser._

    val binExp1 = PBinExp(PIntLit(1), "==", PIntLit(1))
    val method1 = PMethod(PIdnDef("m"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PAssert(binExp1)))))
    val original = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(method1), Seq())

    val binExp2 = PBinExp(PIntLit(3), "==", PIntLit(4))
    val method2 = PMethod(PIdnDef("m"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PAssert(binExp2)))))
    val target = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(method2), Seq())

    // val transformed = StrategyBuilder.Ancestor[PNode](
    //   {
    //     case (_: PIntLit, _) =>
    //       PIntLit(3)
    //   }).execute[PProgram](program1)

    case class Context(increment: Int)

    val transformed = StrategyBuilder.RewriteNodeAndContext[PNode, Context](
      {
        case (PIntLit(i), ctx: Context) =>
          (PIntLit(i + ctx.increment), ctx.copy(ctx.increment + 1))
      }
    )

    // assert(transformed === target)

    // Todo:
    // 1) Try with AST nodes, not just parse AST nodes
    // 2) Work with Strategy builder
    // 3) Don't forget to overload "transform" in Node (AST).
  }
}
