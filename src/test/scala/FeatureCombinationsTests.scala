/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver

import scala.language.implicitConversions
import org.scalatest.{Matchers, FunSuite, FlatSpec}
import ast._
import ast.utility.Transformer._

/**
  * Notes from discussing feature unit tests with Malte: 19.02.2016
  *
  * TODO
  *
  * 5. Check QPs: forall is pure VS. forall is QP
  *
  */

class FeatureCombinationsTests extends FunSuite with Matchers {

  /** forall tests */

  test("Forall with trivial body expression") {
    val q0 = Forall( Seq(LocalVarDecl("i", Int)()), Seq(), TrueLit()() )()

    //println(q0)

    simplify(q0) should be (TrueLit()())
    assert(q0.isValid == true)
  }

  test("Forall of the Quantified Permissions form") {
    val q0 = Forall( Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), FieldAccessPredicate(FieldAccess(LocalVar("x")(Ref), Field("a", Int)())(), FullPerm()())() )() )()

    //println(q0)

    assert(q0.isValid == true)
  }

  test("Forall with magic wand in body expression") {
    val q1 = Forall( Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), MagicWand(TrueLit()(), TrueLit()())() )() )()
    val q2 = Forall( Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), Implies(TrueLit()(), MagicWand(TrueLit()(), TrueLit()())())() )() )()

    //println(q1)
    //println(q2)

    assert(q1.isValid == false)
    assert(q2.isValid == false)
  }

  test("Forall with predicate application in body expression") {
    val pred = PredicateAccess(Seq(LocalVar("x")(Ref)), "pred")(NoPosition, NoInfo)
    val perm = FullPerm()()
    val q1 = Forall(Seq(LocalVarDecl("i", Int)()), Seq(), PredicateAccessPredicate(pred, perm)())()

    //println(q1)

    assert(q1.isValid == false)
  }

  test("Forall with ForPerm in body expression") {
    val pred = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val q = ForPerm( LocalVarDecl("y", Ref)(), Seq(pred), TrueLit()() )()
    val p = Forall(Seq(LocalVarDecl("i", Int)()), Seq(), q)()

    //println(p)

    assert(p.isValid == false)
  }

  /** forperm tests */

  test("ForPerm predicate correctness checks") {
    val pred0 = Predicate("ooo", Seq(), Option(TrueLit()()))()
    val q0 = ForPerm( LocalVarDecl("y", Ref)(), Seq(pred0), TrueLit()() )()

    //println(pred0)
    //println(q0)

    val pred1 = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val q1 = ForPerm( LocalVarDecl("y", Ref)(), Seq(pred1), TrueLit()() )()

    //println(pred1)
    //println(q1)

    val pred2 = Predicate("ofo", Seq(LocalVarDecl("x", Int)()), Option(TrueLit()()))()
    val q2 = ForPerm( LocalVarDecl("y", Ref)(), Seq(pred2), TrueLit()() )()

    //println(pred2)
    //println(q2)

    val pred3 = Predicate("oof", Seq(LocalVarDecl("x1", Ref)(), LocalVarDecl("x2", Ref)()), Option(TrueLit()()))()
    val q3 = ForPerm( LocalVarDecl("y", Ref)(), Seq(pred3), TrueLit()() )()

    //println(pred3)
    //println(q3)

    assert(q0.isValid == false)
    assert(q1.isValid == true)
    assert(q2.isValid == false)
    assert(q3.isValid == false)
  }

  test("ForPerm with Perm in body expression") {
    val pred = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val pred_acc = PredicateAccess(Seq(LocalVar("x")(Ref)), pred)()
    val q = ForPerm( LocalVarDecl("y", Ref)(), Seq(pred), PermGtCmp(CurrentPerm(pred_acc)(), NoPerm()())() )()

    //println(q)

    assert(q.isValid == false)
  }

  /** predicate tests */
  test("Predicate with perm") {
    val pred_acc = PredicateAccess(Seq(LocalVar("x")(Ref)), "pred")(NoPosition, NoInfo)
    val perm = CurrentPerm(pred_acc)()
    val pred2 = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(perm))()

    //println(pred2)

    assert(pred2.isValid == false)
  }

  test("Predicate with forperm") {
    val pred1 = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val q = ForPerm( LocalVarDecl("y", Ref)(), Seq(pred1), TrueLit()() )()
    val pred2 = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(q))()

    //println(pred2)

    assert(pred2.isValid == false)
  }

  /** magic wand tests */
  test("Magic wand with forperm") {
    val pred = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val pred_acc = PredicateAccess(Seq(), pred)()
    val q = ForPerm( LocalVarDecl("y", Ref)(), Seq(pred), PermGtCmp(CurrentPerm(pred_acc)(), NoPerm()())() )()
    val wand0 = MagicWand(TrueLit()(), TrueLit()())()
    val wand1 = MagicWand(q, TrueLit()())()
    val wand2 = MagicWand(TrueLit()(), q)()

    //println(wand0)
    //println(wand1)
    //println(wand2)

    assert(wand0.isValid == true)
    assert(wand1.isValid == false)
    assert(wand2.isValid == false)
  }

  test("Magic wand with Quantified Permissions") {
    val wand1 = MagicWand(TrueLit()(), Forall(Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), FieldAccessPredicate(FieldAccess(LocalVar("x")(Ref), Field("a", Int)())(), FullPerm()())())() )())()
    val wand2 = MagicWand(Forall(Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), FieldAccessPredicate(FieldAccess(LocalVar("x")(Ref), Field("a", Int)())(), FullPerm()())())() )(), TrueLit()())()

    //println(wand1)
    //println(wand2)

    assert(wand1.isValid == false)
    assert(wand2.isValid == false)
  }

  /** function tests */
  test("Function with magic wand") {
    val wand = MagicWand(TrueLit()(), TrueLit()())()
    val f0 = Function("bar", Seq(LocalVarDecl("x", Int)()), Bool, Seq(), Seq(), Option(TrueLit()()))()
    val f1 = Function("foo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(wand), Seq(), Option(TrueLit()()))()
    val f2 = Function("ofo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(wand), Option(TrueLit()()))()
    val f3 = Function("oof", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(), Option(wand))()

    //println(f0)
    //println(f1)
    //println(f2)
    //println(f3)

    assert(f0.isValid == true)
    assert(f1.isValid == false)
    assert(f2.isValid == false)
    assert(f3.isValid == false)
  }

  test("Function with perm expression") {
    val pred_acc = PredicateAccess(Seq(LocalVar("x")(Ref)), "pred")(NoPosition, NoInfo)
    val perm = CurrentPerm(pred_acc)()

    val body_exp = PermGeCmp(perm, NoPerm()())()
    val f1 = Function("foo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(perm), Seq(), Option(TrueLit()()))()
    val f2 = Function("ofo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(perm), Option(TrueLit()()))()
    val f3 = Function("oof", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(), Option(body_exp))()

    //println(f1)
    //println(f2)
    //println(f3)

    assert(f1.isValid == false)
    assert(f2.isValid == false)
    assert(f3.isValid == false)
  }

  test("Function with forperm") {
    val pred = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val q = ForPerm( LocalVarDecl("y", Ref)(), Seq(pred), TrueLit()() )()
    val f1 = Function("foo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(q), Seq(), Option(TrueLit()()))()
    val f2 = Function("ofo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(q), Option(TrueLit()()))()
    val f3 = Function("oof", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(), Option(q))()

    //println(f1)
    //println(f2)
    //println(f3)

    assert(f1.isValid == false)
    assert(f2.isValid == false)
    assert(f3.isValid == false)
  }
}

