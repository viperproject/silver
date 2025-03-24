// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite

import scala.language.implicitConversions
import org.scalatest.matchers.should.Matchers
import viper.silver.ast._
import viper.silver.ast.utility.Simplifier._

class SimplifierTests extends AnyFunSuite with Matchers {

  test("cond") {

    val a = LocalVar("a", Bool)()
    val b = LocalVar("a", Bool)()
    val acc = PredicateAccessPredicate(
      PredicateAccess(Nil, "pred")(),
      None
    )()
    val tru = TrueLit()()

    // Non-pure conditional should be converted into implication
    simplify(CondExp(a,tru,acc)()) should be(Implies(Not(a)(), acc)())

    // Pure conditional can be converted into disjunction
    simplify(CondExp(a,tru,b)()) should be(Or(a, b)())

    simplify(CondExp(a,b,tru)()) should be(Implies(a, b)())

  }

  test("div") {
    simplify(Div(0, 0)()) should be(Div(0, 0)())
    simplify(Div(8, 2)()) should be(4: IntLit)
    simplify(Div(-3, 2)()) should be(Div(-3, 2)())
    simplify(Div(3, 2)()) should be(1: IntLit)
    simplify(Div(3, -2)()) should be(Div(3, -2)())
  }

  test("mod") {
    simplify(Mod(0, 0)()) should be (Mod(0, 0)())
    simplify(Mod(8, 3)()) should be (2: IntLit)
    simplify(Mod(3, 8)()) should be (3: IntLit)
    simplify(Mod(8, -3)()) should be (Mod(8, -3)())
    simplify(Mod(3, -8)()) should be (Mod(3, -8)())
    simplify(Mod(-8, 3)()) should be (Mod(-8, 3)())
    simplify(Mod(-3, 8)()) should be (Mod(-3, 8)())
    simplify(Mod(-8, -3)()) should be (Mod(-8, -3)())
    simplify(Mod(-3, -8)()) should be (Mod(-3, -8)())
  }

  test("equality") {
    val seqAcc = SeqIndex(EmptySeq(Int)(), 0: IntLit)()
    // Do not simplify away definedness issues.
    simplify(EqCmp(seqAcc, seqAcc)()) should be(EqCmp(seqAcc, seqAcc)())
  }

  implicit def int2IntLit(i: Int): IntLit = IntLit(i)()
}
