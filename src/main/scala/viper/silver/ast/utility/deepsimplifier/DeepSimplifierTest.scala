package viper.silver.ast.utility.deepsimplifier

import org.scalatest.funsuite.AnyFunSuite

import scala.language.implicitConversions
import org.scalatest.matchers.should.Matchers
import viper.silver.ast.DomainBinExp.unapply
import viper.silver.ast.{Node, _}
import viper.silver.ast.utility.deepsimplifier.DeepSimplifier._

import scala.collection.mutable.ArrayBuffer

class DeepSimplifierTest extends AnyFunSuite with Matchers{

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

  test("test14") {
    val a = LocalVar("a", Bool)()
    val z = LocalVar("z", Bool)()
    val b = Or(Not(Not(a)())(), a)()
    val c = Or(Not(a)(), a)()
    val d = Or(Not(Not(a)())(), Not(Not(Not(Not(z)())())())())()

    println(d.children)

    pfRecSimplify(d)

    true should be(true)
  }


}
