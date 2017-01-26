package viper.silver.ast.utility

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import viper.silver.ast._
import viper.silver.ast.utility.Nesting.Nesting

import scala.language.implicitConversions

class ChildMatch[+N]() {

}

case class cN[N]() extends ChildMatch[N] {}

object ** extends ChildMatch

object ? extends ChildMatch

object Nesting extends Enumeration {
  type Nesting = Value
  val Start, Deep, Direct = Value
}

case class Quantity(q: Int = 1) {}

object Quantity {
  def star = Quantity(-1)

  def plus = Quantity(-2)
}

class RegexStrategy[N <: Rewritable[N], C](matchSeq: Seq[(Nesting, Match[N])], p: PartialFunction[(N, ContextC[N, Seq[C]]), N]) extends StrategyInterface[N] {

  val matchedNodes = collection.mutable.HashSet.empty[(C, N)]


  def goFurther(node: N, m: Match[N]): Boolean = m match {
    case nodeMatch: n[N] => nodeMatch.valid(node)
    case rewriteMatch: r[N] => rewriteMatch.valid(node)
    case nodePredicate: nP[N] => nodePredicate.valid(node)
    case goIntoChild:intoChild[N] => goIntoChild.valid(node).isDefined
    case _ => true
  }



  override def execute[T <: N](node: N): T = {

    node.asInstanceOf[T]
  }
}

class TRegex[N <: Rewritable[N], C](private val matchers: Seq[(Nesting, Match[N])] = Seq.empty[(Nesting, Match[N])]) {

  def |->(p: PartialFunction[(N, ContextC[N, Seq[C]]), N]): RegexStrategy[N, C] = {
    new RegexStrategy[N, C](matchers, p)
  }

  def %(m: Match[N]): TRegex[N, C] = {
    if (matchers.isEmpty) {
      new TRegex(matchers ++ Seq((Nesting.Start, m)))
    }
    else {
      println("Only use % for starting a regex")
      this
    }
  }

  def >>(m: Match[N]): TRegex[N, C] = {
    new TRegex(matchers ++ Seq((Nesting.Deep, m)))
  }

  def >(m: Match[N]): TRegex[N, C] = {
    new TRegex(matchers ++ Seq((Nesting.Direct, m)))
  }


}

class SlimRegex[N <: Rewritable[N]](private val matchers: Seq[(Nesting, Match[N])] = Seq.empty[(Nesting, Match[N])]) {

  def |->(p: PartialFunction[N, N]): Strategy[N, SimpleContext[N]] = {
    StrategyBuilder.SlimStrategy[N](p)
  }

  def %(m: Match[N]): SlimRegex[N] = {
    if (matchers.isEmpty) {
      new SlimRegex(matchers ++ Seq((Nesting.Start, m)))
    }
    else {
      println("Only use % for starting a regex")
      this
    }
  }

  def >>(m: Match[N]): SlimRegex[N] = new SlimRegex(matchers ++ Seq((Nesting.Deep, m)))

  def >(m: Match[N]): SlimRegex[N] = new SlimRegex(matchers ++ Seq((Nesting.Direct, m)))

}

case class StrategyFromRegex[N <: Rewritable[N], C]() {
  def @>>(m: Match[N]): TRegex[N, C] = new TRegex[N, C] % m
}

class Match[+N]() {
  var quantity: Quantity = Quantity(1)

  def *(): Match[N] = {
    quantity = Quantity.star;
    this
  }

  def +(): Match[N] = {
    quantity = Quantity.plus;
    this
  }

  def ^(i: Int): Match[N] = {
    quantity = Quantity(i);
    this
  }
}

case class n[N]() extends Match[N] {
  def valid(n: Any): Boolean = n.isInstanceOf[N]
}

case class r[N]() extends Match[N] {
  def valid(n: Any): Boolean = n.isInstanceOf[N]
}

case class c[N](acc: N => Any) extends Match[N] {
  def valid(n: Any): Option[Any] = {
    if (n.isInstanceOf[N]) {
      Some(acc(n.asInstanceOf[N]))
    } else {
      None
    }
  }
}

case class intoChild[N](selector: N => Any) extends Match[N] {
  def valid(n: Any): Option[Any] = {
    if (n.isInstanceOf[N]) {
      Some(selector(n.asInstanceOf[N]))
    } else {
      None
    }
  }
}

case class matchChildren[N](s: ChildMatch[N]*) extends Match[N] {}

case class nP[N](p: N => Boolean) extends Match[N] {
  def valid(n: Any): Boolean = {
    if (n.isInstanceOf[N]) {
      p(n.asInstanceOf[N])
    } else {
      false
    }
  }
}

object TRegex {

  implicit def viperRegex(m: Match[Node]): SlimRegex[Node] = {
    new SlimRegex[Node] % m
  }
}


class Test {
  //val t = new TreeRegexBuilder[Node, Exp]()
  StrategyFromRegex[Node, Exp] @>> intoChild[Method](_.pres.head) >> n[Implies] > matchChildren[Or](**).* >> n[Implies] |-> { case (o: Or, c) => Or(o.left, c.custom.head)() }

}
