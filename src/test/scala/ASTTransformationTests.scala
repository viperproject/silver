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

class ASTTransformationTests extends FunSuite {
  object frontend extends SilFrontend {
    def configureVerifier(args: Seq[String]): SilFrontendConfig = ???
    def createVerifier(fullCmd: String): Verifier = ???
  }

  test("Testing support to arbitrary collection types of children node - Example 1") {
    import viper.silver.ast._
    import viper.silver.ast.utility._

    val shared = FalseLit()()
    val sharedAST = And(Not(shared)(), shared)()

    val strat = ViperStrategy.CustomContext[Int](
      {
        case (FalseLit(), c) => if (c == 1) (TrueLit()(), c) else (FalseLit()(), c)
        case (n: Not, i) => (n, i + 1)
      }, 0)

    val res = strat.execute[Exp](sharedAST)

    // Check that both true lits are no longer of the same instance
    res match {
      case And(Not(t1), t2) =>
        assert(t1 == TrueLit()())
        assert(t2 == FalseLit()())
      case _ => assert(false)
    }
  }

  test("Testing support to arbitrary collection types of children node - Example 2") {
    // Transforms this code:
    //   assert 1 == 1
    //
    // Into this program:
    //   assert 3 == 3

    import viper.silver.parser._

    val binExp1 = PBinExp(PIntLit(1), "==", PIntLit(1))
    val binExp2 = PBinExp(PIntLit(3), "==", PIntLit(3))

    case class Context(increment: Int)

    val transformed = StrategyBuilder.RewriteNodeAndContext[PNode, Context](
      {
        case (PIntLit(i), ctx: Context) =>
          (PIntLit(i + ctx.increment), ctx.copy(ctx.increment + 1))
      }, Context(2)).execute[PNode](binExp1)

    assert(transformed === binExp2)
  }

  test("Rewriting nodes and updating context during parse AST traversal - Example 1") {
     // Transforms this code:
     // method m()
     // {
     //   assert 1 == 1
     // }
     //
     // Into this program:
     // method m()
     // {
     //   assert 3 == 3
     // }

     import viper.silver.parser._

     val binExp1 = PBinExp(PIntLit(1), "==", PIntLit(1))
     val method1 = PMethod(PIdnDef("m"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PAssert(binExp1)))))
     val original = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(method1), Seq(), Seq())

     val binExp2 = PBinExp(PIntLit(3), "==", PIntLit(3))
     val method2 = PMethod(PIdnDef("m"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(PAssert(binExp2)))))
     val target = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(), Seq(), Seq(method2),  Seq(), Seq())

     case class Context(increment: Int)

     val transformed = StrategyBuilder.RewriteNodeAndContext[PNode, Context](
       {
         case (PIntLit(i), ctx: Context) =>
           (PIntLit(i + ctx.increment), ctx.copy(ctx.increment + 1)) // Notice that this new context won't
       }, Context(2)).execute[PNode](original)                       // affect its sibling literal node

     assert(transformed === target)
   }

  test("Rewriting nodes and updating context during parse AST traversal - Example 2") {
    // Transform this program:
    // function f(x: Int, y: Int): Int
    // method m()
    // {
    //   assume f(1, 1) == f(1, f(1, f(1, 1)))
    // }
    //
    // Into this one:
    // function f(x: Int, y: Int): Int
    // method m()
    // {
    //   assume f(2, 1) == f(2, f(3, f(4, 1)))
    // }

    import viper.silver.parser._

    val function = PFunction(PIdnDef("f"), Seq(PFormalArgDecl(PIdnDef("x"), TypeHelper.Int), PFormalArgDecl(PIdnDef("y"), TypeHelper.Int)), TypeHelper.Int, Seq(), Seq(), None)
    val assume1 = PAssume(PBinExp(PCall(PIdnUse("f"), Seq(PIntLit(1), PIntLit(1))), "==", PCall(PIdnUse("f"), Seq(PIntLit(1), PCall(PIdnUse("f"), Seq(PIntLit(1), PCall(PIdnUse("f"), Seq(PIntLit(1), PIntLit(1)))))))))
    val method1 = PMethod(PIdnDef("m"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(assume1))))
    val original = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(function), Seq(), Seq(method1),  Seq(), Seq())

    val assume2 = PAssume(PBinExp(PCall(PIdnUse("f"), Seq(PIntLit(2), PIntLit(1))), "==", PCall(PIdnUse("f"), Seq(PIntLit(2), PCall(PIdnUse("f"), Seq(PIntLit(3), PCall(PIdnUse("f"), Seq(PIntLit(4), PIntLit(1)))))))))
    val method2 = PMethod(PIdnDef("m"), Seq(), Seq(), Seq(), Seq(), Some(PSeqn(Seq(assume2))))
    val target = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(function), Seq(), Seq(method2),  Seq(), Seq())

    case class Context(increment: Int)

    val transformed = StrategyBuilder.RewriteNodeAndContext[PNode, Context]({
      case (PCall(fname, PIntLit(i) :: tail, retType), ctx) =>
        (PCall(fname, PIntLit(i + ctx.increment) :: tail, retType), ctx.copy(ctx.increment + 1))
    }, Context(1)).execute[PNode](original)

    assert(transformed === target)
  }

  test("Rewriting nodes and updating context during parse AST traversal - Example 3") {
    // function f(x: Ref): Bool
    //   requires forall y: Int :: y == y

    import viper.silver.parser._

    val requires = PForall(Seq(PFormalArgDecl(PIdnDef("y"), TypeHelper.Int)), Seq(), PBinExp(PIdnUse("y"), "==", PIdnUse("y")))
    val function = PFunction(PIdnDef("f"), Seq(PFormalArgDecl(PIdnDef("x"), TypeHelper.Ref)), TypeHelper.Bool, Seq(requires), Seq(), None)
    val program = PProgram(Seq(), Seq(), Seq(), Seq(), Seq(function), Seq(), Seq(), Seq(), Seq())

    case class Context()

    StrategyBuilder.RewriteNodeAndContext[PNode, Context]({
      case (forall: PForall, c) => {
        val scope = NameAnalyser().namesInScope(program, Some(forall))
        assert(scope === Set("f", "x"))
        (forall, c)
      }
    }, Context()).execute[PNode](function)
  }
}
