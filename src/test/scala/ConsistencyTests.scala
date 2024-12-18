// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import viper.silver.verifier.ConsistencyError
import viper.silver.ast._
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite

class ConsistencyTests extends AnyFunSuite with Matchers {

    /* These tests invoke errors from consistency checks made at AST nodes.
    At the moment, many of these errors cannot be invoked by parsing a Silver program
    because the corresponding checks are also made at the type-checking stage, and thus
    the final AST is never created. It is desirable to remove these duplicate checks from
    the type-checker at some point.
   */

  test("While loop condition"){
    val loop : While = While(IntLit(1)(NoPosition, NoInfo, NoTrafos), Seq(),
      Seqn(Seq(), Seq())(NoPosition, NoInfo, NoTrafos))(NoPosition, NoInfo, NoTrafos)
    loop.checkTransitively should be (Seq(
      ConsistencyError("While loop condition must be of type Bool, but found Int", NoPosition)))
  }

  test("Missing and duplicate identifiers"){
    val funcapp1 : FuncApp = FuncApp("f1", Seq())(NoPosition, NoInfo, Int, NoTrafos)
    val methodcall1: MethodCall = MethodCall("m2", Seq(), Seq())(NoPosition, NoInfo, NoTrafos)
    val method1 : Method = Method("m1", Seq(), Seq(), Seq(), Seq(),
      Some(Seqn(Seq[Stmt](LocalVarAssign(LocalVar("i", Int)(NoPosition, NoInfo, NoTrafos), funcapp1)(NoPosition, NoInfo,
        NoTrafos), Goto("lbl1")(NoPosition, NoInfo, NoTrafos), methodcall1), Seq())(NoPosition, NoInfo, NoTrafos)))(NoPosition, NoInfo, NoTrafos)
    val prog : Program = Program(Seq(), Seq(Field("j", Int)(NoPosition, NoInfo, NoTrafos), Field("j", Bool)(NoPosition, NoInfo, NoTrafos)), Seq(), Seq(), Seq(method1), Seq())(NoPosition, NoInfo, NoTrafos)

    prog.checkTransitively should be (Seq(
      ConsistencyError("Duplicate identifier `j` found.", NoPosition),
      ConsistencyError("Local variable i not found.", NoPosition),
      ConsistencyError("No matching identifier f1 found of type Function.", NoPosition),
      ConsistencyError("No matching identifier lbl1 found of type Label.", NoPosition),
      ConsistencyError("No matching identifier m2 found of type Method.", NoPosition)))
  }

  test("Type mismatched identifiers"){
    val funcapp1 : FuncApp = FuncApp("f1", Seq())(NoPosition, NoInfo, Int, NoTrafos)
    val method1 : Method = Method("m1", Seq(), Seq(), Seq(), Seq(),
      Some(Seqn(Seq[Stmt](LocalVarAssign(LocalVar("i", Int)(NoPosition, NoInfo, NoTrafos), funcapp1)(NoPosition, NoInfo,
        NoTrafos), LocalVarAssign(LocalVar("j", Int)(NoPosition, NoInfo, NoTrafos), IntLit(5)(NoPosition))(NoPosition, NoInfo,
        NoTrafos)), Seq(LocalVarDecl("i", Bool)(NoPosition)))(NoPosition, NoInfo, NoTrafos)))(NoPosition, NoInfo, NoTrafos)
    val method2: Method = Method("j", Seq(), Seq(), Seq(), Seq(), Some(Seqn(Seq(), Seq())(NoPosition)))(NoPosition)
    val prog : Program = Program(Seq(), Seq(Field("f1", Int)(NoPosition, NoInfo, NoTrafos)), Seq(), Seq(), Seq(method1, method2), Seq())(NoPosition, NoInfo, NoTrafos)

    prog.checkTransitively should be (Seq(
      ConsistencyError("No matching local variable i found with type Int, instead found Bool.", NoPosition),
      ConsistencyError("No matching identifier f1 found of type Function, instead found of type Field.", NoPosition),
      ConsistencyError("No matching local variable j found with type Int, instead found other identifier of type Method.", NoPosition)))
  }

  test("Conditional expression"){
    val condexp1 : CondExp = CondExp(BoolLit(true)(NoPosition, NoInfo, NoTrafos),
      IntLit(5)(NoPosition, NoInfo, NoTrafos), FuncApp("f1", Seq())(NoPosition, NoInfo, Bool, NoTrafos))(NoPosition, NoInfo, NoTrafos)

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
      Program(domains    = Seq(), fields     = Seq(), functions  = Seq(), predicates = Seq(), methods    = Seq(callee, caller), extensions = Seq())()

    program.checkTransitively shouldBe Seq(
      ConsistencyError("Arguments List() are not assignable to formal arguments List(x: Ref) of method callee", NoPosition),
      ConsistencyError("Arguments List(null, null) are not assignable to formal arguments List(x: Ref) of method callee", NoPosition),
      ConsistencyError("Arguments List(true) are not assignable to formal arguments List(x: Ref) of method callee", NoPosition)
    )
  }

  test("Function call") {
    val func =
      Function(
        name          = "f",
        formalArgs    = Seq(LocalVarDecl("x", Int)()),
        typ           = Int,
        pres          = Seq(),
        posts         = Seq(),
        body          = None
      )()

    val pred =
      Predicate(
        name          = "P",
        formalArgs    = Seq(LocalVarDecl("x", Int)()),
        body          = None
      )()

    val callerIntVarDecl = LocalVarDecl("intRes", Int)()
    val callerIntVar = LocalVar("intRes", Int)()
    val callerBoolVarDecl = LocalVarDecl("boolRes", Bool)()
    val callerBoolVar = LocalVar("boolRes", Bool)()

    val callerBody =
      Seqn(
        Seq(
          // Wrong: function name
          LocalVarAssign(callerIntVar, FuncApp("g", Seq(callerIntVar))(NoPosition, NoInfo, Int, NoTrafos))(),
          // Wrong: zero arguments
          LocalVarAssign(callerIntVar, FuncApp("f", Seq())(NoPosition, NoInfo, Int, NoTrafos))(),
          // Wrong: wrong return type
          LocalVarAssign(callerBoolVar, FuncApp("f", Seq(callerIntVar))(NoPosition, NoInfo, Bool, NoTrafos))(),
          // Wrong: wrong argument type
          LocalVarAssign(callerIntVar, FuncApp("f", Seq(callerBoolVar))(NoPosition, NoInfo, Int, NoTrafos))()
        ),
        Seq()
      )()

    val callerPosts =
      Seq(
        // Wrong: zero arguments
        PredicateAccessPredicate(PredicateAccess(Seq(), "P")(), Some(FullPerm()()))(),
        // Wrong: wrong argument type
        PredicateAccessPredicate(PredicateAccess(Seq(callerBoolVar), "P")(), None)(),
        // Correct
        PredicateAccessPredicate(PredicateAccess(Seq(callerIntVar), "P")(), None)()
      )

    val caller =
      Method(
        name          = "caller",
        formalArgs    = Seq(),
        formalReturns = Seq(callerIntVarDecl, callerBoolVarDecl),
        pres          = Seq(),
        posts         = callerPosts,
        body          = Some(callerBody)
      )()

    val program =
      Program(domains    = Seq(), fields     = Seq(), functions  = Seq(func), predicates = Seq(pred), methods    = Seq(caller), extensions = Seq())()

    program.checkTransitively shouldBe Seq(
      ConsistencyError("Function f with formal arguments List(x: Int) cannot be applied to provided arguments List().", NoPosition),
      ConsistencyError("No matching function f found of return type Bool, instead found with return type Int.", NoPosition),
      ConsistencyError("Function f with formal arguments List(x: Int) cannot be applied to provided arguments List(boolRes).", NoPosition),
      ConsistencyError("Predicate P with formal arguments List(x: Int) cannot be used with provided arguments List().", NoPosition),
      ConsistencyError("Predicate P with formal arguments List(x: Int) cannot be used with provided arguments List(boolRes).", NoPosition),
      ConsistencyError("No matching identifier g found of type Function.", NoPosition)
    )
  }

  test("Domain function call") {
    val func =
      DomainFunc(
        name       = "f",
        formalArgs = Seq(LocalVarDecl("x", Int)()),
        typ        = Int
      )(NoPosition, NoInfo, "MyDomain", NoTrafos)

    val domain = Domain(
      name      = "MyDomain",
      functions = Seq(func),
      axioms    = Seq(),
      typVars   = Seq()
    )()

    val callerIntVarDecl = LocalVarDecl("intRes", Int)()
    val callerIntVar = LocalVar("intRes", Int)()
    val callerBoolVarDecl = LocalVarDecl("boolRes", Bool)()
    val callerBoolVar = LocalVar("boolRes", Bool)()

    val callerBody =
      Seqn(
        Seq(
          // Wrong: function name
          LocalVarAssign(callerIntVar, DomainFuncApp(funcname="g", Seq(callerIntVar), Map())(NoPosition, NoInfo, Int, "MyDomain", NoTrafos))(),
          // Wrong: domain name
          LocalVarAssign(callerIntVar, DomainFuncApp(funcname="f", Seq(callerIntVar), Map())(NoPosition, NoInfo, Int, "WrongDomain", NoTrafos))(),
          // Wrong: zero arguments
          LocalVarAssign(callerIntVar, DomainFuncApp(funcname="f", Seq(), Map())(NoPosition, NoInfo, Int, "MyDomain", NoTrafos))(),
          // Wrong: wrong return type
          LocalVarAssign(callerBoolVar, DomainFuncApp(funcname="f", Seq(callerIntVar), Map())(NoPosition, NoInfo, Bool, "MyDomain", NoTrafos))(),
          // Wrong: wrong argument type
          LocalVarAssign(callerIntVar, DomainFuncApp(funcname="f", Seq(callerBoolVar), Map())(NoPosition, NoInfo, Int, "MyDomain", NoTrafos))()
        ),
        Seq()
      )()

    val caller =
      Method(
        name          = "caller",
        formalArgs    = Seq(),
        formalReturns = Seq(callerIntVarDecl, callerBoolVarDecl),
        pres          = Seq(),
        posts         = Seq(),
        body          = Some(callerBody)
      )()

    val program =
      Program(domains    = Seq(domain), fields     = Seq(), functions  = Seq(), predicates = Seq(), methods    = Seq(caller), extensions = Seq())()

    program.checkTransitively shouldBe Seq(
      ConsistencyError("No domain function named g found in the program.", NoPosition),
      ConsistencyError("No matching domain function f found in domain WrongDomain, instead found in domain MyDomain.", NoPosition),
      ConsistencyError("Domain function f with formal arguments List(x: Int) cannot be applied to provided arguments List().", NoPosition),
      ConsistencyError("No matching domain function f found of return type Bool, instead found with return type Int.", NoPosition),
      ConsistencyError("Domain function f with formal arguments List(x: Int) cannot be applied to provided arguments List(boolRes).", NoPosition),
      ConsistencyError("No matching identifier g found of type DomainFunc.", NoPosition)
    )
  }

  test("Testing if Forall AST nodes have implication as expression") {

    val f = Field("f", Int)()
    val forall = Forall(Seq(LocalVarDecl("i", Int)()), Seq(), CondExp(FalseLit()(), TrueLit()(), FieldAccessPredicate(FieldAccess(LocalVar("r", Ref)(), f)(), Some(FullPerm()()))())())()

    forall.checkTransitively shouldBe Seq(
      ConsistencyError("Quantified permissions must have an implication as expression, with the access predicate in its right-hand side.", NoPosition)
    )
  }

  test("Testing if Forall AST nodes have at least one quantified variable, all variables are mentioned in " +
    "the trigger, and each trigger expression contains at least one quantified variable.") {

    val f = Function("f", Seq(LocalVarDecl("i", Int)()), Int, Seq(), Seq(), None)()
    val forallNoVar = Forall(Seq(), Seq(), TrueLit()())()
    val forallUnusedVar = Forall(Seq(LocalVarDecl("i", Int)(), LocalVarDecl("j", Int)()), Seq(Trigger(Seq(FuncApp(f, Seq(LocalVar("j", Int)()))()))()), TrueLit()())()
    val forallNoVarTrigger = Forall(Seq(LocalVarDecl("i", Int)()), Seq(Trigger(Seq(FuncApp(f, Seq(LocalVar("i", Int)()))(), FuncApp(f, Seq(IntLit(0)()))()))()), TrueLit()())()

    forallNoVar.checkTransitively shouldBe Seq(
      ConsistencyError("Quantifier must have at least one quantified variable.", NoPosition)
    )

    forallUnusedVar.checkTransitively shouldBe Seq(
      ConsistencyError("Variable i is not mentioned in one or more triggers.", NoPosition)
    )

    forallNoVarTrigger.checkTransitively shouldBe Seq(
      ConsistencyError("Trigger expression f(0) does not contain any quantified variable.", NoPosition)
    )
  }

  test("Domain types and backend types refer only to existing domains and are used correctly.") {
    val f1 = Function("f1", Seq(LocalVarDecl("i", DomainType("nonexisting", Map())(Seq()))()), Int, Seq(), Seq(), None)()
    val f2 = Function("f2", Seq(LocalVarDecl("i", BackendType("nonexisting", Map()))()), Int, Seq(), Seq(), None)()
    val f3 = Function("f3", Seq(LocalVarDecl("i", DomainType("existing2", Map())(Seq()))()), Int, Seq(), Seq(), None)()
    val f4 = Function("f4", Seq(LocalVarDecl("i", BackendType("existing1", Map()))()), Int, Seq(), Seq(), None)()

    val d1 = Domain("existing1", Seq(), Seq(), Seq(), None)()
    val d2 = Domain("existing2", Seq(), Seq(), Seq(), Some(Map("SMTLIL" -> "Bool")))()

    val p1 = Program(domains = Seq(), fields = Seq(), functions = Seq(f1), predicates = Seq(), methods = Seq(), extensions = Seq())()
    p1.checkTransitively shouldBe Seq(
      ConsistencyError("DomainType references non-existent domain nonexisting.", NoPosition)
    )

    val p2 = Program(domains = Seq(), fields = Seq(), functions = Seq(f2), predicates = Seq(), methods = Seq(), extensions = Seq())()
    p2.checkTransitively shouldBe Seq(
      ConsistencyError("BackendType references non-existent domain nonexisting.", NoPosition)
    )

    val p3 = Program(domains = Seq(d2), fields = Seq(), functions = Seq(f3), predicates = Seq(), methods = Seq(), extensions = Seq())()
    p3.checkTransitively shouldBe Seq(
      ConsistencyError("DomainType existing2 references domain with interpretation; must use BackendType instead.", NoPosition)
    )

    val p4 = Program(domains = Seq(d1), fields = Seq(), functions = Seq(f4), predicates = Seq(), methods = Seq(), extensions = Seq())()
    p4.checkTransitively shouldBe Seq(
      ConsistencyError("BackendType existing1 references domain without interpretation; must use DomainType instead.", NoPosition)
    )
  }
}
