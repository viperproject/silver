// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast._
import viper.silver.ast.utility.Expressions

/** Tests of Expressions.instantiateVariables (Sanitizer.replaceFreeVariablesInExpression): variables bound
  * in the expression are renamed to avoid capture, and hide replaced variables with the same names.
  */
class SanitizerTests extends AnyFunSuite {
  private val x = LocalVarDecl("x", Ref)()

  test("A let variable named like a variable of the replacing expression is renamed") {
    // let b == (null) in b != x, with b for x
    val b = LocalVarDecl("b", Ref)()
    val exp = Let(b, NullLit()(), NeCmp(b.localVar, x.localVar)())()
    Expressions.instantiateVariables(exp, Seq(x), Seq(LocalVar("b", Ref)()), Set("b")) match {
      case Let(v, NullLit(), NeCmp(left, right)) =>
        assert(v.name != "b")
        assert(left == v.localVar)
        assert(right == LocalVar("b", Ref)())
      case other => fail(s"Unexpected result $other")
    }
  }

  test("A let variable is renamed in nested lets and quantifiers") {
    // let b == (null) in (let c == (b) in forall i: Int :: c != x), with b for x
    val b = LocalVarDecl("b", Ref)()
    val c = LocalVarDecl("c", Ref)()
    val i = LocalVarDecl("i", Int)()
    val exp = Let(b, NullLit()(), Let(c, b.localVar, Forall(Seq(i), Seq(), NeCmp(c.localVar, x.localVar)())())())()
    Expressions.instantiateVariables(exp, Seq(x), Seq(LocalVar("b", Ref)()), Set("b")) match {
      case Let(v, NullLit(), Let(w, bound, Forall(_, _, NeCmp(left, right)))) =>
        assert(v.name != "b")
        assert(bound == v.localVar)
        assert(w.name == "c")
        assert(left == w.localVar)
        assert(right == LocalVar("b", Ref)())
      case other => fail(s"Unexpected result $other")
    }
  }

  test("A let variable that does not clash is not renamed") {
    // let b == (null) in b != x, with y for x
    val b = LocalVarDecl("b", Ref)()
    val exp = Let(b, NullLit()(), NeCmp(b.localVar, x.localVar)())()
    val result = Expressions.instantiateVariables(exp, Seq(x), Seq(LocalVar("y", Ref)()), Set("y"))
    assert(result == Let(b, NullLit()(), NeCmp(b.localVar, LocalVar("y", Ref)())())())
  }

  test("A quantified variable named like a variable of the replacing expression is renamed") {
    // forall i: Ref :: i != x, with i for x
    val i = LocalVarDecl("i", Ref)()
    val exp = Forall(Seq(i), Seq(), NeCmp(i.localVar, x.localVar)())()
    Expressions.instantiateVariables(exp, Seq(x), Seq(LocalVar("i", Ref)()), Set("i")) match {
      case Forall(Seq(v), _, NeCmp(left, right)) =>
        assert(v.name != "i")
        assert(left == v.localVar)
        assert(right == LocalVar("i", Ref)())
      case other => fail(s"Unexpected result $other")
    }
  }

  test("The expression bound by a let is rewritten outside of the let's scope") {
    // let b == (null) in (let b == (b) in b != x), with y for x (shadowing lets can be built as ASTs)
    val b = LocalVarDecl("b", Ref)()
    val exp = Let(b, NullLit()(), Let(b, b.localVar, NeCmp(b.localVar, x.localVar)())())()
    Expressions.instantiateVariables(exp, Seq(x), Seq(LocalVar("y", Ref)()), Set("y")) match {
      case Let(outer, NullLit(), Let(inner, bound, NeCmp(left, right))) =>
        assert(bound == outer.localVar)
        assert(inner.name != outer.name)
        assert(left == inner.localVar)
        assert(right == LocalVar("y", Ref)())
      case other => fail(s"Unexpected result $other")
    }
  }

  test("A variable bound with the name of a replaced variable is not replaced") {
    // let x == (1) in x == 1, with a for x
    val xInt = LocalVarDecl("x", Int)()
    val exp = Let(xInt, IntLit(1)(), EqCmp(xInt.localVar, IntLit(1)())())()
    Expressions.instantiateVariables(exp, Seq(xInt), Seq(LocalVar("a", Int)()), Set("a")) match {
      case Let(v, IntLit(_), EqCmp(left, IntLit(_))) => assert(left == v.localVar)
      case other => fail(s"Unexpected result $other")
    }
  }

  test("A variable bound with the name of a variable replaced by itself is renamed consistently") {
    // let x == (1) in x == 1, with x for x
    val xInt = LocalVarDecl("x", Int)()
    val exp = Let(xInt, IntLit(1)(), EqCmp(xInt.localVar, IntLit(1)())())()
    Expressions.instantiateVariables(exp, Seq(xInt), Seq(xInt.localVar), Set("x")) match {
      case Let(v, IntLit(_), EqCmp(left, IntLit(_))) => assert(left == v.localVar)
      case other => fail(s"Unexpected result $other")
    }
  }

  test("Variables that would capture are renamed even if no scope is given") {
    // let b == (null) in b != x, with b for x, using the overload of instantiateVariables without a scope
    val b = LocalVarDecl("b", Ref)()
    val exp = Let(b, NullLit()(), NeCmp(b.localVar, x.localVar)())()
    Expressions.instantiateVariables(exp, Seq(x.localVar), Seq(LocalVar("b", Ref)())) match {
      case Let(v, NullLit(), NeCmp(left, right)) =>
        assert(v.name != "b")
        assert(left == v.localVar)
        assert(right == LocalVar("b", Ref)())
      case other => fail(s"Unexpected result $other")
    }
  }

  test("A renamed variable does not capture a free variable of the expression") {
    // let b == (null) in b != x && b$0 == null, with b for x (without a scope)
    val b = LocalVarDecl("b", Ref)()
    val b0 = LocalVar("b$0", Ref)()
    val exp = Let(b, NullLit()(), And(NeCmp(b.localVar, x.localVar)(), EqCmp(b0, NullLit()())())())()
    Expressions.instantiateVariables(exp, Seq(x.localVar), Seq(LocalVar("b", Ref)())) match {
      case Let(v, NullLit(), And(NeCmp(left, right), EqCmp(free, NullLit()))) =>
        assert(v.name != "b" && v.name != "b$0")
        assert(left == v.localVar)
        assert(right == LocalVar("b", Ref)())
        assert(free == b0)
      case other => fail(s"Unexpected result $other")
    }
  }

  test("A replaced variable in the expression bound by a let is replaced outside of the let's scope") {
    // let b == (x) in b != null, with b for x
    val b = LocalVarDecl("b", Ref)()
    val exp = Let(b, x.localVar, NeCmp(b.localVar, NullLit()())())()
    Expressions.instantiateVariables(exp, Seq(x), Seq(LocalVar("b", Ref)()), Set("b")) match {
      case Let(v, bound, NeCmp(left, NullLit())) =>
        assert(v.name != "b")
        assert(bound == LocalVar("b", Ref)())
        assert(left == v.localVar)
      case other => fail(s"Unexpected result $other")
    }
  }

  test("A quantified variable with the name of a replaced variable is not replaced") {
    // forall x: Int :: x > 0, with a for x
    val xInt = LocalVarDecl("x", Int)()
    val exp = Forall(Seq(xInt), Seq(), GtCmp(xInt.localVar, IntLit(0)())())()
    Expressions.instantiateVariables(exp, Seq(xInt), Seq(LocalVar("a", Int)()), Set("a")) match {
      case Forall(Seq(v), _, GtCmp(left, IntLit(_))) => assert(left == v.localVar)
      case other => fail(s"Unexpected result $other")
    }
  }

  test("A quantified variable with the name of a variable replaced by itself is renamed consistently") {
    // forall x: Int :: x > 0, with x for x
    val xInt = LocalVarDecl("x", Int)()
    val exp = Forall(Seq(xInt), Seq(), GtCmp(xInt.localVar, IntLit(0)())())()
    Expressions.instantiateVariables(exp, Seq(xInt), Seq(xInt.localVar), Set("x")) match {
      case Forall(Seq(v), _, GtCmp(left, IntLit(_))) => assert(left == v.localVar)
      case other => fail(s"Unexpected result $other")
    }
  }
}
