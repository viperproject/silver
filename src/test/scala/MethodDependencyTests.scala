/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import org.scalatest._
import viper.silver.ast.{And, Bool, Domain, Field, FieldAccess, FieldAccessPredicate, FullPerm, FuncApp, Function, Hashable, LocalVar, LocalVarDecl, Method, MethodCall, Predicate, PredicateAccess, PredicateAccessPredicate, Program, Ref, Seqn, TrueLit, Unfold, While}

class MethodDependencyTests extends FunSuite with Matchers {


  /** Testing dependency analysis for caching for the following Viper program:

        field f0: Bool
        field f1: Bool
        field f2: Bool
        field f3: Bool
        filed f4: Bool

        domain D0 { }

        function fun0(): Bool
        function fun1(): Bool
        function fun2(): Bool
        function fun3(): Bool
        function fun4(x:Ref): Bool // for testing transitivity
          requires acc(x.f4)

        predicate p0()
        predicate p1()
        predicate p2()
        predicate p3()
        predicate p4(x:Ref) { fun4(x) }

        method m0(x:Ref)
          requires acc(p4(x),write)
        {
          m1()
        }
        method m1()

        method test(x: Ref)
          requires acc(x.f0) && fun0() && acc(p0(),write)
          ensures  acc(x.f1) && fun1() && acc(p1(),write)
        {
          unfold p2
          while ( true )
            invariant x.f2
          {
            while ( true )
              invariant fun2()
            {
              m0(x)
            }
          }
        }

   * The method test must depend on all AST nodes but the following: fun3, p3, m1.
   */

  val D0: Domain = Domain("D0", Seq(), Seq(), Seq())()
  val f0: Field = Field("f0", Bool)()
  val f1: Field = Field("f1", Bool)()
  val f2: Field = Field("f2", Bool)()
  val f3: Field = Field("f3", Bool)()
  val f4: Field = Field("f4", Bool)()
  val fun0: Function = Function("fun0", Seq(), Bool, Seq(), Seq(), None, None)()
  val fun1: Function = Function("fun1", Seq(), Bool, Seq(), Seq(), None, None)()
  val fun2: Function = Function("fun2", Seq(), Bool, Seq(), Seq(), None, None)()
  val fun3: Function = Function("fun3", Seq(), Bool, Seq(), Seq(), None, None)()
  val fun4: Function = Function("fun4", Seq(LocalVarDecl("x", Ref)()), Bool, Seq(FieldAccessPredicate(FieldAccess(LocalVar("x")(Ref), Field("f4", Bool)())(),FullPerm()())()), Seq(), None, None)()
  val p0: Predicate = Predicate("p0", Seq(), None)()
  val p1: Predicate = Predicate("p1", Seq(), None)()
  val p2: Predicate = Predicate("p2", Seq(), None)()
  val p3: Predicate = Predicate("p3", Seq(), None)()
  val p4: Predicate = Predicate("p4", Seq(LocalVarDecl("x", Ref)()), Some(FuncApp(fun4, Seq(LocalVar("x")(Ref)))()))()
  val m1: Method = Method("m1", Seq(), Seq(), Seq(), Seq(), Some(Seqn(Seq(), Seq())()))()
  val m0: Method = Method("m0", Seq(LocalVarDecl("x", Ref)()), Seq(), Seq(PredicateAccessPredicate(PredicateAccess(Seq(LocalVar("x")(Ref)), p4.name)(), FullPerm()())()), Seq(), Some(Seqn(Seq(MethodCall(m1,Seq(),Seq())()), Seq())()))()
  val test: Method = Method("test",
    Seq(LocalVarDecl("x", Ref)()),
    Seq(),
    // preconditions:
    Seq(And(FieldAccessPredicate(FieldAccess(LocalVar("x")(Ref), f0)(), FullPerm()())(), And(FuncApp(fun0, Seq())(), PredicateAccessPredicate(PredicateAccess(Seq(), p0.name)(), FullPerm()())())())()),
    // postconditions:
    Seq(And(FieldAccessPredicate(FieldAccess(LocalVar("x")(Ref), f1)(), FullPerm()())(), And(FuncApp(fun1, Seq())(), PredicateAccessPredicate(PredicateAccess(Seq(), p1.name)(), FullPerm()())())())()),
    // body of the method:
    Some(Seqn(Seq(
      Unfold(PredicateAccessPredicate(PredicateAccess(Seq(), p2.name)(), FullPerm()())())(),
      While(TrueLit()(), Seq(FieldAccess(LocalVar("x")(Ref), f2)()), Seqn(Seq(
        // body of the outer loop
        While(TrueLit()(), Seq(FuncApp(fun2, Seq())()), Seqn(Seq(
          // body of the inner loop
          MethodCall(m0, Seq(LocalVar("x")(Ref)), Seq())()
        ), Seq())())()
      ), Seq())())()
    ), Seq())()))()

  val p: Program = Program(Seq(D0), Seq(f0, f1, f2, f3, f4), Seq(fun0, fun1, fun2, fun3, fun4), Seq(p0, p1, p2, p3, p4), Seq(m0, m1, test))()

  //println(p)

  val global_deps: List[Hashable] = List(D0, f0,f1,f2,f3,f4)
  val via_pre_deps: List[Hashable] = List(fun0, p0)
  val via_post_deps: List[Hashable] = List(fun1, p1)
  val via_body_deps: List[Hashable] = List(fun2, p2) ++ m0.formalArgs ++ m0.formalReturns ++ m0.pres ++ m0.posts
  val transitive_deps: List[Hashable] = List(fun4, p4)
  val must_be_deps: List[Hashable] = global_deps ++ via_pre_deps ++ via_post_deps ++ via_body_deps ++ transitive_deps
  val must_not_be_deps: List[Hashable] = List(fun3, p3, m0.body.get, m1)

  val computed_deps = p.getDependencies(p, test)


  val test_prefix = s"Test Dependency Analysis"

  test(s"$test_prefix: are the AST node selectors valid?") {
    // Check that nodes don't appear in both lists at the same time.
    p.deepCollect {
      case n if must_be_deps.contains(n) && must_not_be_deps.contains(n) =>
        fail(s"AST node ```$n``` is present in both lists: `must_be_deps` and `must_not_be_deps`.")
    }
  }

  test(s"$test_prefix: are fields and domains global dependencies?") {
    global_deps.foreach {
      case n =>
        if ( !computed_deps.contains(n) )
          fail(s"AST node ```$n``` is expected to be a global dependency of all methods, but is not present in the result of `getDependencies`.")
    }
  }

  test(s"$test_prefix: are the dependencies from preconditions encountered for?") {
    via_pre_deps.foreach {
      case n =>
        if ( !computed_deps.contains(n) )
          fail(s"AST node ```$n``` is expected to be a dependency from the precondition of ```$test```, but is not present in the result of `getDependencies`.")
    }
  }

  test(s"$test_prefix: are the dependencies from postconditions encountered for?") {
    via_post_deps.foreach {
      case n =>
        if ( !computed_deps.contains(n) )
          fail(s"AST node ```$n``` is expected to be a dependency from the postcondition of ```$test```, but is not present in the result of `getDependencies`.")
    }
  }

  test(s"$test_prefix: are the dependencies from method's body encountered for?") {
    via_body_deps.foreach {
      case n =>
        if ( !computed_deps.contains(n) )
          fail(s"AST node ```$n``` is expected to be a dependency from the body of ```$test```, but is not present in the result of `getDependencies`.")
    }
  }

  test(s"$test_prefix: are transitive dependencies encountered for?") {
    transitive_deps.foreach {
      case n =>
        if ( !computed_deps.contains(n) )
          fail(s"AST node ```$n``` is expected to be a transitive dependency of ```$test```, but is not present in the result of `getDependencies`.")
    }
  }

  test(s"$test_prefix: do we get too many dependencies?") {
    computed_deps.foreach {
      case n =>
        if ( !must_be_deps.contains(n) || must_not_be_deps.contains(n) )
          fail(s"AST node ```$n``` is not expected to be a dependency of ```$test```, but is present in the result of `getDependencies`.")
    }
  }

  // If the following test is the only one to fail, the above tests are probably messed up.
  test(s"$test_prefix: sanity checks") {
    computed_deps.size should be (must_be_deps.size)
  }
}
