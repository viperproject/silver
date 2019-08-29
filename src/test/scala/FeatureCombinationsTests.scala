// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.{Matchers, FunSuite}
import viper.silver.ast._
import viper.silver.ast.utility.Simplifier._

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

    simplify(q0) should be (TrueLit()())
    assert(q0.isValid)
  }

  test("Forall of the Quantified Permissions form") {
    val q0 = Forall( Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), FieldAccessPredicate(FieldAccess(LocalVar("x", Ref)(), Field("a", Int)())(), FullPerm()())() )() )()

    assert(q0.isValid)
  }

  test("Forall with magic wand in body expression") {
    val q1 = Forall( Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), MagicWand(TrueLit()(), TrueLit()())() )() )()
    val q2 = Forall( Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), Implies(TrueLit()(), MagicWand(TrueLit()(), TrueLit()())())() )() )()

    assert(!q1.isValid)
    assert(!q2.isValid)
  }

  test("Forall with predicate application in body expression") {
    val pred = PredicateAccess(Seq(LocalVar("x", Ref)()), "pred")(NoPosition, NoInfo, NoTrafos)
    val perm = FullPerm()()
    val q1 = Forall(Seq(LocalVarDecl("i", Int)()), Seq(), PredicateAccessPredicate(pred, perm)())()

    assert(!q1.isValid)
  }

  test("Forall with ForPerm in body expression") {
    val pred = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val predAccess = PredicateAccess(Seq(LocalVar("y", Ref)()), pred)(NoPosition, NoInfo, NoTrafos)
    val q = ForPerm( Seq(LocalVarDecl("y", Ref)()), predAccess, TrueLit()() )()
    val p = Forall(Seq(LocalVarDecl("i", Int)()), Seq(), q)()

    assert(!p.isValid)
  }

  /** forperm tests */

  test("ForPerm with Perm in body expression") {
    val pred = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val pred_acc = PredicateAccess(Seq(LocalVar("y", Ref)()), pred.name)()
    val q = ForPerm( Seq(LocalVarDecl("y", Ref)()), pred_acc, PermGtCmp(CurrentPerm(pred_acc)(), NoPerm()())() )()

    assert(!q.isValid)
  }

  /** predicate tests */
  test("Predicate with perm") {
    val pred_acc = PredicateAccess(Seq(LocalVar("x", Ref)()), "pred")(NoPosition, NoInfo, NoTrafos)
    val perm = CurrentPerm(pred_acc)()
    val pred2 = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(perm))()

    assert(!pred2.isValid)
  }

  test("Predicate with forperm") {
    val pred1 = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val pred_acc = PredicateAccess(Seq(LocalVar("y", Ref)()), pred1.name)()
    val q = ForPerm( Seq(LocalVarDecl("y", Ref)()), pred_acc, TrueLit()() )()
    val pred2 = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(q))()

    assert(!pred2.isValid)
  }

  /** magic wand tests */
  test("Magic wand with forperm") {
    val pred = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val pred_acc = PredicateAccess(Seq(), pred.name)()
    val q = ForPerm( Seq(LocalVarDecl("y", Ref)()), pred_acc, PermGtCmp(CurrentPerm(pred_acc)(), NoPerm()())() )()
    val wand0 = MagicWand(TrueLit()(), TrueLit()())()
    val wand1 = MagicWand(q, TrueLit()())()
    val wand2 = MagicWand(TrueLit()(), q)()

    assert(wand0.isValid)
    assert(!wand1.isValid)
    assert(!wand2.isValid)
  }

  test("Magic wand with Quantified Permissions") {
    val wand1 = MagicWand(TrueLit()(), Forall(Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), FieldAccessPredicate(FieldAccess(LocalVar("x", Ref)(), Field("a", Int)())(), FullPerm()())())() )())()
    val wand2 = MagicWand(Forall(Seq(LocalVarDecl("x", Ref)()), Seq(), Implies(TrueLit()(), FieldAccessPredicate(FieldAccess(LocalVar("x", Ref)(), Field("a", Int)())(), FullPerm()())())() )(), TrueLit()())()

    assert(!wand1.isValid)
    assert(!wand2.isValid)
  }

  /** function tests */
  test("Function with magic wand") {
    val wand = MagicWand(TrueLit()(), TrueLit()())()
    val f0 = Function("bar", Seq(LocalVarDecl("x", Int)()), Bool, Seq(), Seq(), Option(TrueLit()()))()
    val f1 = Function("foo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(wand), Seq(), Option(TrueLit()()))()
    val f2 = Function("ofo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(wand), Option(TrueLit()()))()
    val f3 = Function("oof", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(), Option(wand))()

    assert(f0.isValid)
    assert(!f1.isValid)
    assert(!f2.isValid)
    assert(!f3.isValid)
  }

  test("Function with perm expression") {
    val pred_acc = PredicateAccess(Seq(LocalVar("x", Ref)()), "pred")(NoPosition, NoInfo, NoTrafos)
    val perm = CurrentPerm(pred_acc)()

    val body_exp = PermGeCmp(perm, NoPerm()())()
    val f1 = Function("foo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(perm), Seq(), Option(TrueLit()()))()
    val f2 = Function("ofo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(perm), Option(TrueLit()()))()
    val f3 = Function("oof", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(), Option(body_exp))()

    assert(!f1.isValid)
    assert(!f2.isValid)
    assert(!f3.isValid)
  }

  test("Function with forperm") {
    val pred = Predicate("foo", Seq(LocalVarDecl("x", Ref)()), Option(TrueLit()()))()
    val pred_acc = PredicateAccess(Seq(LocalVar("y", Ref)()), pred.name)()
    val q = ForPerm( Seq(LocalVarDecl("y", Ref)()), pred_acc, TrueLit()() )()
    val f1 = Function("foo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(q), Seq(), Option(TrueLit()()))()
    val f2 = Function("ofo", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(q), Option(TrueLit()()))()
    val f3 = Function("oof", Seq(LocalVarDecl("y", Int)()), Bool, Seq(), Seq(), Option(q))()

    assert(!f1.isValid)
    assert(!f2.isValid)
    assert(!f3.isValid)
  }
}

