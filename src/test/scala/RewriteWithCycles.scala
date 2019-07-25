// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.FunSuite
import viper.silver.ast.utility.rewriter.{Rewritable, StrategyBuilder}
import scala.reflect.runtime.{universe => reflection}

class RewriteWithCycles extends FunSuite {


  test("SimpleCycle") {
    val a = SlimGraph[Int](1)
    val b = SlimGraph[Int](10, Seq(a))
    val c = SlimGraph[Int](100, Seq(b))
    a.addChildren(c)

    visitAll[Int](a, _ * 2)
    val res = Seq(a,b,c).foldLeft(0)(_ + _.info)

    assert(res == 222)
  }

  test("ComplexCycle") {
    val a = SlimGraph[Int](1)
    val b = SlimGraph[Int](10)
    val c = SlimGraph[Int](100)
    val d = SlimGraph[Int](1000)


    a.addChildren(b, c)
    b.addChildren(c)
    c.addChildren(a, d)
    d.addChildren(d)

    visitAll[Int](a, _ * 3)
    val res = Seq(a,b,c,d).foldLeft(0)(_ + _.info)

    // we visit c twice (intended because it is a shared node)
    assert( res == 3933)
  }

  // Visit all reachable nodes in the graph and call func on them.
  def visitAll[I : reflection.TypeTag](s:SlimGraph[I], func:I=>I) = {
    val strat = StrategyBuilder.Ancestor[SlimGraph[I]]({
      case (sG, c) => {
        if(c.ancestorList.dropRight(1).contains(sG))
          c.noRec(sG)
        else {
          sG.info = func(sG.info)
          sG
        }
      }
    })
    strat.execute[SlimGraph[I]](s)
  }

}

// Simple graph class. Enough to demonstrate what we want
case class SlimGraph[I](var info: I, var childn: Seq[SlimGraph[I]] = Seq()) extends Rewritable {
  def addChildren(ch: SlimGraph[I]*) = childn ++= ch

  // duplicate must not create a new node but update the old node to keep the circular dependencies
  def duplicate(childr: Seq[AnyRef]): Rewritable = {
    childn = childr.collect {  case s:SlimGraph[I] => s }
    this
  }

  // Otherwise toString crashes from infinite recursion
  override def toString: String = info.toString

}
