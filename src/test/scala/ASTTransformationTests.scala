// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.frontend._
import viper.silver.verifier.Verifier
import viper.silver.ast.NoPosition

class ASTTransformationTests extends AnyFunSuite {
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

    val p = (NoPosition, NoPosition)
    val binExp1 = PBinExp(PIntLit(1)(p), PReserved.implied(PSymOp.EqEq), PIntLit(1)(p))(p)
    val binExp2 = PBinExp(PIntLit(3)(p), PReserved.implied(PSymOp.EqEq), PIntLit(3)(p))(p)

    case class Context(increment: Int)

    val transformed = StrategyBuilder.RewriteNodeAndContext[PNode, Context](
      {
        case (PIntLit(i), ctx: Context) =>
          (PIntLit(i + ctx.increment)(p), ctx.copy(ctx.increment + 1))
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

     val p = (NoPosition, NoPosition)
     val binExp1 = PBinExp(PIntLit(1)(p), PReserved.implied(PSymOp.EqEq), PIntLit(1)(p))(p)
     val method1 = PMethod(Seq(), PReserved.implied(PKw.Method), PIdnDef("m")(p), PGrouped.impliedParen(PDelimited.empty), None, PDelimited.empty, PDelimited.empty, Some(PSeqn(PDelimited.impliedBlock(Seq(PAssert(PReserved.implied(PKw.Assert), binExp1)(p))))(p)))(p)
     val original = PProgram(Nil, Seq(method1))(p, Seq())

     val binExp2 = PBinExp(PIntLit(3)(p), PReserved.implied(PSymOp.EqEq), PIntLit(3)(p))(p)
     val method2 = PMethod(Seq(), PReserved.implied(PKw.Method), PIdnDef("m")(p), PGrouped.impliedParen(PDelimited.empty), None, PDelimited.empty, PDelimited.empty, Some(PSeqn(PDelimited.impliedBlock(Seq(PAssert(PReserved.implied(PKw.Assert), binExp2)(p))))(p)))(p)
     val target = PProgram(Nil, Seq(method2))(p, Seq())

     case class Context(increment: Int)

     val transformed = StrategyBuilder.RewriteNodeAndContext[PNode, Context](
       {
         case (PIntLit(i), ctx: Context) =>
           (PIntLit(i + ctx.increment)(p), ctx.copy(ctx.increment + 1)) // Notice that this new context won't
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

    def commaParen[T <: PNode](args: Seq[T]) = PDelimited.impliedParenComma(args)

    val p = (NoPosition, NoPosition)
    val function = PFunction(Seq(), PReserved.implied(PKw.Function), PIdnDef("f")(p), commaParen(Seq(PFormalArgDecl(PIdnDef("x")(p), PReserved.implied(PSym.Colon), TypeHelper.Int)(p), PFormalArgDecl(PIdnDef("y")(p), PReserved.implied(PSym.Colon), TypeHelper.Int)(p))), PReserved.implied(PSym.Colon), TypeHelper.Int, PDelimited.empty, PDelimited.empty, None)(p)
    val assume1 = PAssume(PReserved.implied(PKw.Assume), PBinExp(PCall(PIdnRef("f")(p), commaParen(Seq(PIntLit(1)(p), PIntLit(1)(p))), None)(p), PReserved.implied(PSymOp.EqEq), PCall(PIdnRef("f")(p), commaParen(Seq(PIntLit(1)(p), PCall(PIdnRef("f")(p), commaParen(Seq(PIntLit(1)(p), PCall(PIdnRef("f")(p), commaParen(Seq(PIntLit(1)(p), PIntLit(1)(p))), None)(p))), None)(p))), None)(p))(p))(p)
    val method1 = PMethod(Seq(), PReserved.implied(PKw.Method), PIdnDef("m")(p), PGrouped.impliedParen(PDelimited.empty), None, PDelimited.empty, PDelimited.empty, Some(PSeqn(PDelimited.impliedBlock(Seq(assume1)))(p)))(p)
    val original = PProgram(Nil, Seq(function, method1))(p, Seq())

    val assume2 = PAssume(PReserved.implied(PKw.Assume), PBinExp(PCall(PIdnRef("f")(p), commaParen(Seq(PIntLit(2)(p), PIntLit(1)(p))), None)(p), PReserved.implied(PSymOp.EqEq), PCall(PIdnRef("f")(p), commaParen(Seq(PIntLit(2)(p), PCall(PIdnRef("f")(p), commaParen(Seq(PIntLit(3)(p), PCall(PIdnRef("f")(p), commaParen(Seq(PIntLit(4)(p), PIntLit(1)(p))), None)(p))), None)(p))), None)(p))(p))(p)
    val method2 = PMethod(Seq(), PReserved.implied(PKw.Method), PIdnDef("m")(p), PGrouped.impliedParen(PDelimited.empty), None, PDelimited.empty, PDelimited.empty, Some(PSeqn(PDelimited.impliedBlock(Seq(assume2)))(p)))(p)
    val target = PProgram(Nil, Seq(function, method2))(p, Seq())

    case class Context(increment: Int)

    val transformed = StrategyBuilder.RewriteNodeAndContext[PNode, Context]({
      case (PCall(fname, args, retType), ctx) if args.inner.length >= 1 && args.inner.head.isInstanceOf[PIntLit] =>
        (PCall(fname, args.update(PIntLit(args.inner.head.asInstanceOf[PIntLit].i + ctx.increment)(p) +: args.inner.tail), retType)(p), ctx.copy(ctx.increment + 1))
    }, Context(1)).execute[PNode](original)

    assert(transformed === target)
  }

  test("Rewriting nodes and updating context during parse AST traversal - Example 3") {
    // function f(x: Ref): Bool
    //   requires forall y: Int :: y == y

    import viper.silver.parser._

    val p = (NoPosition, NoPosition)
    val requires = PForall(PReserved.implied(PKw.Forall), PDelimited.implied(Seq(PLogicalVarDecl(PIdnDef("y")(p), PReserved.implied(PSym.Colon), TypeHelper.Int)(p)), PReserved.implied(PSym.Comma)), PReserved.implied(PSym.ColonColon), Seq(), PBinExp(PIdnUseExp("y")(p), PReserved.implied(PSymOp.EqEq), PIdnUseExp("y")(p))(p))(p)
    val function = PFunction(Seq(), PReserved.implied(PKw.Function), PIdnDef("f")(p), PDelimited.impliedParenComma(Seq(PFormalArgDecl(PIdnDef("x")(p), PReserved.implied(PSym.Colon), TypeHelper.Ref)(p))), PReserved.implied(PSym.Colon), TypeHelper.Bool, PDelimited.implied(Seq(PSpecification(PReserved.implied(PKw.Requires), requires)(p)), None), PDelimited.empty, None)(p)
    val program = PProgram(Nil, Seq(function))(p, Seq())

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
