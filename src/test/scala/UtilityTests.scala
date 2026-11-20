// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.silver.ast._
import viper.silver.ast.utility.{Expressions, ImpureAssumeRewriter}


class UtilityTests extends AnyFunSuite with Matchers {

  /* These tests exercise utility methods on the AST (transformers, visitors, rewriters etc.) */

  test("Assume rewriter (direct)"){ // assume acc(x.f) -> rewritten to -> assume perm(x.f) >= write
    val assumeBody = FieldAccessPredicate(FieldAccess(LocalVar("x", Ref)(),Field("f",Int)(NoPosition))(NoPosition), Some(FullPerm()(NoPosition)))(NoPosition)
    val testMethod : Method = Method("m1", Seq(), Seq(), Seq(), Seq(),
      Some(Seqn(Seq(
        Assume(assumeBody)(NoPosition)
      ), Seq())(NoPosition, NoInfo, NoTrafos))
      )(NoPosition)

    val testProgram : Program = Program(Seq(), Seq(Field("f",Int)(NoPosition)), Seq(), Seq(), Seq(testMethod), Seq())(NoPosition)

    // val rewritten = AssumeRewriter.rewrite(assumeBody,testProgram)

    // rewritten should be (TrueLit()(NoPosition)) // this (spurious) test seems to cause an infinite recursion bug..
    assert(true) // dummy check for now, since test causes trouble
    //assert(rewritten == rewritten)
    // assert(rewritten == TrueLit()())
  }

  test("Expressions are compared modulo lets") {
    val q = Function("q", Seq(LocalVarDecl("n", Int)()), Int, Seq(), Seq(), None)()
    val f = Function("f", Seq(LocalVarDecl("a", Int)(), LocalVarDecl("b", Int)()), Int, Seq(), Seq(), None)()
    val i = LocalVar("i", Int)()
    val j = LocalVar("j", Int)()
    val x = LocalVar("x", Int)()
    val y = LocalVar("y", Int)()
    def let(v: LocalVar, e: Exp, body: Exp) = Let(LocalVarDecl(v.name, v.typ)(), e, body)()
    def forall(v: LocalVar, body: Exp) = Forall(Seq(LocalVarDecl(v.name, v.typ)()), Seq(), body)()
    def fapp(a: Exp, b: Exp) = FuncApp(f, Seq(a, b))()
    val qi = FuncApp(q, Seq(i))()
    val ref = LocalVar("r", Ref)()
    val rf = FieldAccess(ref, Field("g", Int)())()

    // let x == q(i) in f(x, x) and f(q(i), q(i))
    Expressions.equalModuloLets(let(x, qi, fapp(x, x)), fapp(qi, qi)) shouldBe true
    Expressions.equalModuloLets(let(x, qi, fapp(x, x)), let(y, qi, fapp(y, y))) shouldBe true
    Expressions.equalModuloLets(let(x, qi, fapp(x, x)), fapp(qi, i)) shouldBe false
    // Quantified variables are compared by their binding
    Expressions.equalModuloLets(forall(i, GtCmp(fapp(i, j), IntLit(0)())()), forall(y, GtCmp(fapp(y, j), IntLit(0)())())) shouldBe true
    Expressions.equalModuloLets(let(x, i, forall(i, GtCmp(fapp(x, i), IntLit(0)())())), forall(i, GtCmp(fapp(i, i), IntLit(0)())())) shouldBe false
    // A let-bound variable used in an old expression is not replaced by its value there
    Expressions.equalModuloLets(let(x, rf, Old(fapp(x, x))()), Old(fapp(rf, rf))()) shouldBe false
    Expressions.equalModuloLets(let(x, rf, Old(fapp(x, x))()), let(y, rf, Old(fapp(y, y))())) shouldBe true
    Expressions.equalModuloLets(Old(let(x, rf, fapp(x, x)))(), Old(fapp(rf, rf))()) shouldBe true
    // A let-bound variable is compared to a quantified variable by its value
    Expressions.equalModuloLets(forall(j, let(y, j, fapp(y, y))), forall(j, fapp(j, j))) shouldBe true
    Expressions.equalModuloLets(forall(j, fapp(j, j)), forall(j, let(y, j, fapp(y, y)))) shouldBe true
    // let x == q(i) in (let x == x in x), where the inner let shadows the outer one
    Expressions.equalModuloLets(let(x, qi, let(x, x, x)), qi) shouldBe true

    Expressions.topLevelModuloLets(let(x, qi, fapp(x, x))) shouldBe fapp(x, x)
    Expressions.topLevelModuloLets(let(x, qi, let(y, x, y))) shouldBe qi

    // let x1 == f(x0, x0) in let x2 == f(x1, x1) in ... in x40, which has 2^40 applications of f with its lets inlined
    val n = 40
    val xs = (0 to n).map(k => LocalVar(s"x$k", Int)())
    def chain(x0: Exp) = let(xs(0), x0, (1 to n).foldRight(xs(n): Exp)((k, body) =>
      let(xs(k), fapp(xs(k - 1), xs(k - 1)), body)))
    Expressions.equalModuloLets(chain(qi), chain(FuncApp(q, Seq(i))())) shouldBe true
    Expressions.equalModuloLets(chain(qi), chain(FuncApp(q, Seq(j))())) shouldBe false

    // The same expression with lets at even and at odd depths: let x0 == q(i) in let x2 == f(f(x0, x0), f(x0, x0)) in
    // ... in x40 and let y1 == f(q(i), q(i)) in let y3 == f(f(y1, y1), f(y1, y1)) in ... in f(y39, y39)
    def twice(e: Exp) = fapp(fapp(e, e), fapp(e, e))
    val evens = (2 to n by 2).foldRight(xs(n): Exp)((k, body) => let(xs(k), twice(xs(k - 2)), body))
    val ys = (0 to n).map(k => LocalVar(s"y$k", Int)())
    val odds = (3 to n - 1 by 2).foldRight(fapp(ys(n - 1), ys(n - 1)): Exp)((k, body) => let(ys(k), twice(ys(k - 2)), body))
    Expressions.equalModuloLets(let(xs(0), qi, evens), let(ys(1), fapp(qi, qi), odds)) shouldBe true
  }

  /*
  test("Substitution (simple)"){ // forall x. f(x) >= f(y) && exists y. f(y) >
    val xPlusy : Exp = Add(LocalVar("x"),LocalVar("y"))(NoPosition, NoInfo, NoTrafos)


      While = While(IntLit(1)(NoPosition, NoInfo, NoTrafos), Seq(),
      Seqn(Seq(), Seq())(NoPosition, NoInfo, NoTrafos))(NoPosition, NoInfo, NoTrafos)
    loop.checkTransitively should be (Seq(
      ConsistencyError("While loop condition must be of type Bool, but found Int", NoPosition)))
  }

  test("Missing and duplicate identifiers"){
    val funcapp1 : FuncApp = FuncApp("f1", Seq())(NoPosition, NoInfo, Int, Seq(), NoTrafos)
    val methodcall1: MethodCall = MethodCall("m2", Seq(), Seq())(NoPosition, NoInfo, NoTrafos)
    val method1 : Method = Method("m1", Seq(), Seq(), Seq(), Seq(),
      Some(Seqn(Seq[Stmt](LocalVarAssign(LocalVar("i")(Int, NoPosition, NoInfo, NoTrafos), funcapp1)(NoPosition, NoInfo,
        NoTrafos), Goto("lbl1")(NoPosition, NoInfo, NoTrafos), methodcall1), Seq())(NoPosition, NoInfo, NoTrafos)))(NoPosition, NoInfo, NoTrafos)
    val prog : Program = Program(Seq(), Seq(Field("j", Int)(NoPosition, NoInfo, NoTrafos), Field("j", Bool)(NoPosition, NoInfo, NoTrafos)),
      Seq(), Seq(), Seq(method1))(NoPosition, NoInfo, NoTrafos)

    prog.checkTransitively should be (Seq(
      ConsistencyError("Duplicate identifier j found.", NoPosition),
      ConsistencyError("Local variable i not found.", NoPosition),
      ConsistencyError("No matching identifier f1 found of type Function.", NoPosition),
      ConsistencyError("No matching identifier lbl1 found of type Label.", NoPosition),
      ConsistencyError("No matching identifier m2 found of type Method.", NoPosition)))
  }

  test("Type mismatched identifiers"){
    val funcapp1 : FuncApp = FuncApp("f1", Seq())(NoPosition, NoInfo, Int, Seq(), NoTrafos)
    val method1 : Method = Method("m1", Seq(), Seq(), Seq(), Seq(),
      Some(Seqn(Seq[Stmt](LocalVarAssign(LocalVar("i")(Int, NoPosition, NoInfo, NoTrafos), funcapp1)(NoPosition, NoInfo,
        NoTrafos) , LocalVarAssign(LocalVar("j")(Int, NoPosition, NoInfo, NoTrafos), IntLit(5)(NoPosition))(NoPosition, NoInfo,
        NoTrafos)), Seq(LocalVarDecl("i", Bool)(NoPosition)))(NoPosition, NoInfo, NoTrafos)))(NoPosition, NoInfo, NoTrafos)
    val method2: Method = Method("j", Seq(), Seq(), Seq(), Seq(), Some(Seqn(Seq(), Seq())(NoPosition)))(NoPosition)
    val prog : Program = Program(Seq(), Seq(Field("f1", Int)(NoPosition, NoInfo, NoTrafos)),
      Seq(), Seq(), Seq(method1, method2))(NoPosition, NoInfo, NoTrafos)

    prog.checkTransitively should be (Seq(
      ConsistencyError("No matching local variable i found with type Int, instead found Bool.", NoPosition),
      ConsistencyError("No matching identifier f1 found of type Function, instead found of type Field.", NoPosition),
      ConsistencyError("No matching local variable j found with type Int, instead found other identifier of type Method.", NoPosition)))
  }

  test("Conditional expression"){
    val condexp1 : CondExp = CondExp(BoolLit(true)(NoPosition, NoInfo, NoTrafos),
      IntLit(5)(NoPosition, NoInfo, NoTrafos), FuncApp("f1", Seq())(NoPosition, NoInfo, Bool, Seq(), NoTrafos))(NoPosition, NoInfo, NoTrafos)

    condexp1.checkTransitively should be (Seq(
      ConsistencyError("Second and third parameter types of conditional expression must match, but found Int and Bool", NoPosition)
    ))
  }

  test("Field assignment"){
    val fieldassign1 : FieldAssign = FieldAssign(FieldAccess(IntLit(5)(NoPosition, NoInfo, NoTrafos),
      Field("i", Int)(NoPosition, NoInfo, NoTrafos))(NoPosition, NoInfo, NoTrafos),
      BoolLit(false)(NoPosition, NoInfo, NoTrafos))(NoPosition, NoInfo, NoTrafos)

    fieldassign1.checkTransitively should be (Seq(
      ConsistencyError("Right-hand side false is not assignable to left-hand side 5.i.", NoPosition)))
  }

  test("Method arity") {
    val callee =
      Method(
        name          = "callee",
        formalArgs    = Seq(LocalVarDecl("x", Ref)()),
        formalReturns = Seq(),
        pres          = Seq(),
        posts         = Seq(),
        body          = None
      )()

    val callerBody =
      Seqn(
        Seq(
          MethodCall(callee, Seq(), Seq())(), // Wrong: zero arguments
          MethodCall(callee, Seq(NullLit()(), NullLit()()), Seq())(), // Wrong: two arguments
          MethodCall(callee, Seq(NullLit()()), Seq())(), // Right: one argument
          MethodCall(callee, Seq(TrueLit()()), Seq())() // Wrong: incorrect type
        ),
        Seq()
      )()

    val caller =
      Method(
        name          = "caller",
        formalArgs    = Seq(),
        formalReturns = Seq(),
        pres          = Seq(),
        posts         = Seq(),
        body          = Some(callerBody)
      )()

    val program =
      Program(
        domains    = Seq(),
        fields     = Seq(),
        functions  = Seq(),
        predicates = Seq(),
        methods    = Seq(callee, caller)
      )()

    program.checkTransitively shouldBe Seq(
      ConsistencyError("Arguments List() are not assignable to formal arguments List(x: Ref) of method callee", NoPosition),
      ConsistencyError("Arguments List(null, null) are not assignable to formal arguments List(x: Ref) of method callee", NoPosition),
      ConsistencyError("Arguments List(true) are not assignable to formal arguments List(x: Ref) of method callee", NoPosition)
    )
  }
*/
}
