package viper.silver.ast.utility.deepsimplifier

import org.scalatest.funsuite.AnyFunSuite

import scala.language.implicitConversions
import org.scalatest.matchers.should.Matchers
import viper.silver.ast.{Node, _}
import viper.silver.ast.utility.deepsimplifier.DeepSimplifier._

class DeepSimplifierTest extends AnyFunSuite with Matchers{

  test("Cmp1") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Not(EqCmp(a,b)())()

    simplify(c) should be (NeCmp(a,b)())
  }

  test("Cmp2") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Not(NeCmp(a,b)())()

    simplify(c) should be (EqCmp(a,b)())
  }

  test("Cmp3") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Not(GtCmp(a,b)())()

    simplify(c) should be (LeCmp(a,b)())
  }

  test("Cmp4") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Not(GeCmp(a,b)())()

    simplify(c) should be (LtCmp(a,b)())
  }

  test("Cmp5") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Not(LtCmp(a,b)())()

    simplify(c) should be (GeCmp(a,b)())
  }

  test("Cmp6") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Not(LeCmp(a,b)())()

    simplify(c) should be (GtCmp(a,b)())
  }


  test("notnot1") {
    val a = LocalVar("a", Bool)()

    simplify(Not(Not(a)())()) should be (a)
  }


  test("or1"){
    val a = LocalVar("a", Bool)()
    val expr = Or(FalseLit()(), a)()

    simplify(expr) should be (a)
  }

  test("or2"){
    val a = LocalVar("a", Bool)()
    val expr = Or(a, FalseLit()())()

    simplify(expr) should be (a)
  }

  test("or3"){
    val a = LocalVar("a", Bool)()
    val expr = Or(TrueLit()(), a)()

    simplify(expr) should be (TrueLit()())
  }

  test("or4"){
    val a = LocalVar("a", Bool)()
    val expr = Or(a, TrueLit()())()

    simplify(expr) should be (TrueLit()())
  }


  test("and1") {
    val a = LocalVar("a", Bool)()
    val expr = And(TrueLit()(), a)()

    simplify(expr) should be (a)
  }

  test("and2") {
    val a = LocalVar("a", Bool)()
    val expr = And(a, TrueLit()())()

    simplify(expr) should be (a)
  }

  test("and3") {
    val a = LocalVar("a", Bool)()
    val expr = And(FalseLit()(), a)()

    simplify(expr) should be (FalseLit()())
  }

  test("and4") {
    val a = LocalVar("a", Bool)()
    val expr = And(a, FalseLit()())()

    simplify(expr) should be (FalseLit()())
  }

  test("idem1") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = And(And(a,b)(),a)()

    simplify(expr, true) should (be (And(a,b)()) or be (And(b,a)()))
  }

  test("idem2") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = And(b,And(a,b)())()

    simplify(expr, true) should (be (And(a,b)()) or be (And(b,a)()))
  }

  test("idem3"){
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = Or(Or(a,b)(),a)()

    simplify(expr, true) should (be (Or(a,b)()) or be (Or(b,a)()))
  }

  test("idem4"){
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = Or(b,Or(a,b)())()

    simplify(expr, true) should (be (Or(a,b)()) or be (Or(b,a)()))
  }

  //while these do cannot verify if associativity of or/and is being applied, they should catch some cases where associativity is incorrectly applied
  test("assoc1") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = LocalVar("c", Bool)()
    val expr = And(a,And(b,c)())()

    simplify(expr) should (be (And(a,And(b,c)())()) or be (And(a, And(c,b)())()) or be (And(b, And(c,a)())()) or be (And(b, And(a,c)())()) or be (And(c, And(a,b)())()) or be (And(c, And(b,a)())()) or be (And(And(b,c)(), a)()) or be (And(And(c,b)(), a)()) or be (And(And(c,a)(), b)()) or be (And(And(a,c)(), b)()) or be (And(And(a,b)(), c)()) or be (And(And(b,a)(), c)()) )
  }

  test("assoc2") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = LocalVar("c", Bool)()
    val expr = And(And(a, b)(), c)()

    simplify(expr) should (be (And(a,And(b,c)())()) or be (And(a, And(c,b)())()) or be (And(b, And(c,a)())()) or be (And(b, And(a,c)())()) or be (And(c, And(a,b)())()) or be (And(c, And(b,a)())()) or be (And(And(b,c)(), a)()) or be (And(And(c,b)(), a)()) or be (And(And(c,a)(), b)()) or be (And(And(a,c)(), b)()) or be (And(And(a,b)(), c)()) or be (And(And(b,a)(), c)()) )
  }

  test("assoc3") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = LocalVar("c", Bool)()
    val expr = Or(a,Or(b,c)())()

    simplify(expr) should (be (Or(a,Or(b,c)())()) or be (Or(a, Or(c,b)())()) or be (Or(b, Or(c,a)())()) or be (Or(b, Or(a,c)())()) or be (Or(c, Or(a,b)())()) or be (Or(c, Or(b,a)())()) or be (Or(Or(b,c)(), a)()) or be (Or(Or(c,b)(), a)()) or be (Or(Or(c,a)(), b)()) or be (Or(Or(a,c)(), b)()) or be (Or(Or(a,b)(), c)()) or be (Or(Or(b,a)(), c)()) )
  }

  test("assoc4") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = LocalVar("c", Bool)()
    val expr = Or(Or(a, b)(), c)()

    simplify(expr) should (be (Or(a,Or(b,c)())()) or be (Or(a, Or(c,b)())()) or be (Or(b, Or(c,a)())()) or be (Or(b, Or(a,c)())()) or be (Or(c, Or(a,b)())()) or be (Or(c, Or(b,a)())()) or be (Or(Or(b,c)(), a)()) or be (Or(Or(c,b)(), a)()) or be (Or(Or(c,a)(), b)()) or be (Or(Or(a,c)(), b)()) or be (Or(Or(a,b)(), c)()) or be (Or(Or(b,a)(), c)()) )
  }

  test("and11") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = LocalVar("c", Bool)()
    val d = And(a, And(b,c)())()
    val expr = And(And(a,b)(), And(a,c)())()

    simplify(expr, true) should (be (And(a,And(b,c)())()) or be (And(a, And(c,b)())()) or be (And(b, And(c,a)())()) or be (And(b, And(a,c)())()) or be (And(c, And(a,b)())()) or be (And(c, And(b,a)())()) or be (And(And(b,c)(), a)()) or be (And(And(c,b)(), a)()) or be (And(And(c,a)(), b)()) or be (And(And(a,c)(), b)()) or be (And(And(a,b)(), c)()) or be (And(And(b,a)(), c)()) )
  }

  test("or11") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = LocalVar("c", Bool)()
    val d = Or(a, Or(b,c)())()
    val expr = Or(Or(a,b)(), Or(a,c)())()

    simplify(expr, true) should (be (Or(a,Or(b,c)())()) or be (Or(a, Or(c,b)())()) or be (Or(b, Or(c,a)())()) or be (Or(b, Or(a,c)())()) or be (Or(c, Or(a,b)())()) or be (Or(c, Or(b,a)())()) or be (Or(Or(b,c)(), a)()) or be (Or(Or(c,b)(), a)()) or be (Or(Or(c,a)(), b)()) or be (Or(Or(a,c)(), b)()) or be (Or(Or(a,b)(), c)()) or be (Or(Or(b,a)(), c)()) )
  }

  test("impl1") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = Implies(a, b)()

    simplify(expr) should be (Implies(a, b)())
  }

  test("impl2") {
    val a = FalseLit()()
    val b = LocalVar("b", Bool)()
    val expr = Implies(a, b)()

    simplify(expr) should be (TrueLit()())
  }

  test("impl3") {
    val a = TrueLit()()
    val b = LocalVar("b", Bool)()
    val expr = Implies(a, b)()

    simplify(expr, true) should be (b)
  }

  test("impl4") {
    val a = LocalVar("a", Bool)()
    val c = LocalVar("c", Bool)()
    val d = Implies(a,c)()
    val expr = Implies(a, d)()

    simplify(expr, true) should be (Implies(a, c)())
  }

  test("impl5") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Implies(a,b)()
    val d = Implies(Not(a)(),b)()
    val expr = And(c, d)()

    simplify(expr, true) should be (b)
  }

  test("impl6") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Implies(a,b)()
    val d = Implies(Not(a)(),b)()
    val expr = And(c, d)()

    simplify(expr, true) should be (b)
  }

  test("impl7") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = Implies(Not(b)(), Not(a)())()

    simplify(expr) should be (Implies(a, b)())
  }

  test("and21") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = Not(And(a,Not(b)())())()

    simplify(expr) should be (Or(Not(a)(), b)())
  }

  test("and22") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = And(Not(a)(),Not(b)())()

    simplify(expr) should be (Not(Or(a,b)())())
  }

  test("dem1") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = Not(Or(Not(a)(),Not(b)())())()

    simplify(expr) should be (And(a,b)())
  }

  test("dem2") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = And(Not(a)(),Not(b)())()

    simplify(expr) should be (Not(Or(a,b)())())
  }

  test("dem3") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = Not(And(Not(a)(),Not(b)())())()

    simplify(expr) should be (Or(a,b)())
  }

  test("dem4") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = Or(Not(a)(),Not(b)())()

    simplify(expr) should be (Not(And(a,b)())())
  }


  test("eq1 assumeWelldefinedness") {
    val x = LocalVar("x", Bool)()
    val expr = EqCmp(x, x)()

    simplify(expr, true) should be (TrueLit()())
  }

  test("eq2") {
    val expr = EqCmp(BoolLit(true)(), BoolLit(true)())()

    simplify(expr) should be (BoolLit(true)())
  }

  test("eq2bis") {
    val expr = EqCmp(BoolLit(true)(), BoolLit(false)())()

    simplify(expr) should be (BoolLit(false)())
  }

  test("eq3") {
    val a = LocalVar("a", Bool)()
    val expr = EqCmp(FalseLit()(), a)()

    simplify(expr) should be (Not(a)())
  }

  test("eq4") {
    val a = LocalVar("a", Bool)()
    val expr = EqCmp(a, FalseLit()())()

    simplify(expr) should be (Not(a)())
  }

  test("eq5") {
    val a = LocalVar("a", Bool)()
    val expr = EqCmp(TrueLit()(), a)()

    simplify(expr) should be (a)
  }

  test("eq6") {
    val a = LocalVar("a", Bool)()
    val expr = EqCmp(a, TrueLit()())()

    simplify(expr) should be (a)
  }

  test("eq7") {
    val expr = EqCmp(IntLit(32)(), IntLit(32)())()

    simplify(expr) should be (BoolLit(true)())
  }

  test("eq7bis") {
    val expr = EqCmp(IntLit(32)(), IntLit(31)())()

    simplify(expr) should be (BoolLit(false)())
  }

  test("eq8") {
    val expr = EqCmp(NullLit()(), NullLit()())()

    simplify(expr) should be (TrueLit()(expr.pos, expr.info))
  }



  test("eq10") {
    val expr = NeCmp(BoolLit(true)(), BoolLit(true)())()

    simplify(expr) should be (BoolLit(false)())
  }

  test("eq10bis") {
    val expr = NeCmp(BoolLit(true)(), BoolLit(false)())()

    simplify(expr) should be (BoolLit(true)())
  }

  test("eq11") {
    val a = LocalVar("a", Bool)()
    val expr = NeCmp(FalseLit()(), a)()

    simplify(expr) should be (a)
  }

  test("eq12") {
    val a = LocalVar("a", Bool)()
    val expr = NeCmp(a, FalseLit()())()

    simplify(expr) should be (a)
  }

  test("eq13") {
    val a = LocalVar("a", Bool)()
    val expr = NeCmp(TrueLit()(), a)()

    simplify(expr) should be (Not(a)())
  }

  test("eq14") {
    val a = LocalVar("a", Bool)()
    val expr = NeCmp(a, TrueLit()())()

    simplify(expr) should be (Not(a)())
  }

  test("eq15") {
    val expr = NeCmp(IntLit(32)(), IntLit(32)())()

    simplify(expr) should be (BoolLit(false)())
  }
  test("eq15bis") {
    val expr = NeCmp(IntLit(32)(), IntLit(31)())()

    simplify(expr) should be (BoolLit(true)())
  }

  test("eq16") {
    val expr = NeCmp(NullLit()(), NullLit()())()

    simplify(expr) should be (FalseLit()())
  }

  test("eq17 assumeWelldefinedness") {
    val x = LocalVar("x", Bool)()
    val expr = NeCmp(x, x)()

    simplify(expr, true) should be (FalseLit()())
  }
  test("eq17bis assumeWelldefinedness") {
    val expr = NeCmp(IntLit(5)(), IntLit(5)())()

    simplify(expr) should be (FalseLit()())
  }
  test("eq17ter assumeWelldefinedness") {
    val expr = NeCmp(IntLit(5)(), IntLit(6)())()

    simplify(expr) should be (TrueLit()())
  }


  test("eq20 assumeWelldefinedness") {
    val a = LocalVar("a", Int)()
    val b = LocalVar("b", Int)()

    val expr = And(
      EqCmp(a, b)(),
      NeCmp(a, b)()
    )()

    simplify(expr, true) should be (FalseLit()())
  }


  test("eq21 assumeWelldefinedness") {
    val a = LocalVar("a", Int)()
    val b = LocalVar("b", Int)()

    val expr = Or(
      EqCmp(a, b)(),
      NeCmp(a, b)()
    )()

    simplify(expr, true) should be (TrueLit()())
  }

  test("ce1") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val ifFalse = BoolLit(false)()
    val expr = CondExp(TrueLit()(), a, b)()

    simplify(expr) should be (a)
  }

  test("ce2") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val ifFalse = BoolLit(false)()
    val expr = CondExp(FalseLit()(), a, b)()

    simplify(expr) should be (b)
  }

  test("ce3 assumeWelldefinedness") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = CondExp(b, a, a)()

    simplify(expr, true) should be (a)
  }

  test("ce4") {
    val a = LocalVar("a", Bool)()
    val expr = CondExp(a, FalseLit()(), TrueLit()())()

    simplify(expr) should be (Not(a)(expr.pos, expr.info))
  }

  test("ce5") {
    val a = LocalVar("a", Bool)()
    val expr = CondExp(a, TrueLit()(), FalseLit()())()

    simplify(expr) should be (a)
  }

  test("ce6") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = CondExp(a, FalseLit()(), Not(a)())()

    simplify(expr) should be (Not(Or(a,a)())())
  }
  test("ce6bis assumeWelldefinedeness") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = CondExp(a, FalseLit()(), Not(a)())()

    simplify(expr, true) should be (Not(a)())
  }

  test("ce7") {
    val a = LocalVar("a", Bool)()
    val z = BoolLit(false)() //z must be pure/z.isPure == true
    val expr = CondExp(a, TrueLit()(), z)()

    simplify(expr) should be (a) //(a || false) = a
  }

  test("ce8") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = CondExp(a, b, FalseLit()())()

    simplify(expr) should be (And(a, b)())
  }

  test("ce9") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val expr = CondExp(a, b, TrueLit()())()

    simplify(expr) should be (Implies(a, b)())
  }











  test("and5 assumeWelldefinedness"){
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = LocalVar("c", Bool)()
    val d = And(a, And(b,c)())()
    val e = And(And(a,b)(), And(a,c)())()

    simplify(e, true) should (be (And(And(a,b)(),c)()) or be (And(And(a,b)(),c)()))
  }

  test("implies1"){
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val d = And(Implies(a, b)(), Implies(Not(a)(), b)())()

    simplify(d, true) should be (b)
  }
  test("not3"){
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val d = And(Implies(a, b)(), Implies(Not(a)(), b)())()

    simplify(d, true) should be (b)
  }
  test("implies2"){
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val d = Implies(a, b)()

    simplify(d) should be (d)
  }
  test("implies3"){
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val z = NullLit()()
    val y = NullLit()()
    val c = LocalVar("c", Bool)()
    val aa = EqCmp(a, z)()
    val bb = EqCmp(b, y)()
    val d = And(Implies(aa, c)(), Implies(Not(aa)(), c)())()

    simplify(d, true) should be(c)
  }

  test("test1") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Or(Or(Not(a)(), Not(b)())(), FalseLit()())()
    simplify(c) should (be (Not(And(a,b)())()) or be (Not(And(b,a)())()))
  }

  test("test14") {
    val a = LocalVar("a", Bool)()
    val z = LocalVar("z", Bool)()
    val d = Or(Not(Not(a)())(), Not(Not(Not(Not(z)())())())())()
    val f = Or(d, Not(Not(Not(Not(FalseLit()())())())())())()

    simplify(f) should (be (Or(a,z)()) or be (Or(z,a)()))
  }

  test("eqcmp1") {
    val a = LocalVar("a", Bool)()
    val d = EqCmp(a, a)()
    simplify(d, true) should be(TrueLit()(d.pos, d.info))
  }

  test("eqcmp2") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = NeCmp(a, b)()
    val d = EqCmp(a, b)()
    val e = And(c, d)()
    val f = Or(c, d)()

    simplify(e, true) should be(FalseLit()(e.pos, e.info))
    simplify(f, true) should be(TrueLit()(f.pos, f.info))
  }

  test("eqcmp3") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = NeCmp(a, b)()
    val d = EqCmp(a, b)()
    val e = And(c, d)()
    val f = Or(c, d)()

    simplify(e, true) should be(FalseLit()(e.pos, e.info))
    simplify(f, true) should be(TrueLit()(f.pos, f.info))
  }

  test("neue") {

    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = LocalVar("c", Bool)()

    simplify (And(Implies(a, b)(), Implies(a, c)())()) should be (Implies(a, And(b, c)())())

    simplify (And(Implies(a, b)(), Implies(Not(a)(), b)())()) should be (And(Implies(a,b)(),Implies(Not(a)(), b)())())
    simplify (And(Implies(a, b)(), Implies(Not(a)(), b)())(), true) should be (b)

    simplify (And(a, Implies(a, b)())()) should be (And(a, b)())
  }






  /*test("test1") {

    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()


    simplify(Implies(a, b)()) should be(Implies(a, b)())

    println(Implies(a, b)())
    println(simplify(Implies(a, b)()))
  }

  test("test2") {

    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()


    simplify(Or(a, b)()) should be(Implies(a, b)())

    println(Or(a, b)())
    println(simplify(Implies(a, b)()))
  }

  test("test3") {

    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()

    val c = Or(a, b)()

    val d = LocalVar("a", Bool)()
    val e = LocalVar("b", Bool)()

    val f = Or(d, e)()


    c should be(f)

    println(c)
    println(f)
  }

  /*test("test4") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()

    val c = Or(a, b)()

    contains(c) should be(true)
  }*/

  test("test4") {
    val a = LocalVar("a", Bool)()
    val b = Not(Not(a)())()

    println(b)
    //println(genSimp(b))

    true should be(true)
  }

  test("test5") {
    val a = LocalVar("a", Bool)()
    val b = And(a, a)()

    println(b)
    println(a.getClass)

    true should be(true)
  }

  test("test6") {
    val a = LocalVar("a", Bool)()
    val b = Not(Not(a)())()
    val c = Not(Not(b)())()
    val tru = TrueLit()()
    val d = Or(c, tru)()

    println(d)
    println(simplify(d))

    true should be(true)
  }

  test("test7") {
    val a = LocalVar("a", Bool)()
    val b = Not(Not(Not(a)())())()

    println(b)
    println(recursiveSimplify(b))

    true should be(true)
  }

  test("test8") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = And(a, Not(a)())()
    val d = And(b, c)()


    println(d)
    println(d.size)

    true should be(true)
  }

  test("test9") {
    val a = LocalVar("a", Bool)()
    val b = Not(Not(a)())()
    val c = And(a, Not(a)())()
    val d = And(b, c)()


    println(d)
    println(recursiveSimplify(d))

    true should be(true)
  }

  test("test10") {
    val a = LocalVar("a", Bool)()
    val b = LocalVar("b", Bool)()
    val c = Or(a, Not(a)())()
    val d = Or(b, c)()


    println(d)
    println()
    println(pfSimplify(d))

    true should be(true)
  }

  test("test11") {
    val a = LocalVar("a", Bool)()
    val b = Not(Not(a)())()

    println(b)
    println(pfSimplify(b))

    true should be(true)
  }

  test("test12") {
    val a = LocalVar("a", Bool)()
    val tru = TrueLit()()
    val othertru = TrueLit()()
    val b = Not(Not(a)())()
    val c = Or(othertru, tru)()

    println(c)
    println(treeSize(a))
    println(treeSize(tru))
    println(treeSize(c))
    println(pfSimplify(c))

    true should be(true)
  }

  test("test13") {
    val a = LocalVar("a", Bool)()
    val b = Or(Not(Not(a)())(), a)()
    val c = Or(Not(a)(), a)()

    val buf = ArrayBuffer[Node](a, b, c)

    println(getShortest(buf))

    true should be(true)
  }

   */




}
