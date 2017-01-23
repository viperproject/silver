/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver

import scala.language.implicitConversions
import org.scalatest.{FunSuite, Matchers}
import ast._
import ast.utility._
import ast.If




class TreeRegexBuilder[N, C] {

  def NoRec[NODE <: N](o: NODE): NODE = ???


  def context[NODE <: N](trafo:NODE=>C):Match[NODE, N, C] = ??? // Extract context
  def node[NODE <: N]():Match[NODE, N, C] = ??? // Node must be there
  def matchOn[NODE <: N]():Match[NODE, N, C] = ??? // Match on this node
  def intoChild[NODE <: N](selector:NODE=>N):Match[NODE, N, C] = ???
  def matchChildren[NODE <: N](s: ChildMatch[_, N, C]*):Match[NODE, N, C] = ???
  def nodePred[NODE <: N](p: NODE=>Boolean):Match[NODE, N, C] = ???


  def >>[NODE <: N](m: Match[_, NODE, C]):ChildMatch[NODE, N, C] = ???
  def ?[NODE <: N]:ChildMatch[NODE, N, C] = ???
  def childNode[NODE <: N]:ChildMatch[NODE, N, C] = ???
  def **[NODE <: N]: ChildMatch[NODE, N, C] = ???

}

class ChildMatch[Node <: N, N, C] {

}



class Match[NODE <: N, N, C] {
  def *(): Match[_, N, C] = ???
  def +(): Match[_, N, C] = ???
  def ^(i: Int): Match[_, N, C] = ???

  def >>(m: Match[_ ,N, C]):Match[_, N, C] = ???

  def >(m:Match[_, N, C]):Match[_, N, C] = ???

  def |->(p: PartialFunction[(N, Seq[C]), N]):Strategy[N, ContextC[N, C]] = ???
}

class nodeMatch[Node <: N, N, C] extends Match[Node, N, C] {

}

class rewriteMatch[Node <: N, N, C] extends Match[Node, N, C] {

}

class contextMatch[Node <: N, N, C](val acc:Node=>C) extends Match[Node, N, C] {

}

class childrenMatch[Node <: N, N, C](selector:Node=>Seq[Match[Node, N, C]]) {

}

class Test {
  val t = new TreeRegexBuilder[Node, Exp]()
  t.intoChild[Method](_.pres.head) >> t.node[Implies] > t.matchChildren[Or](t >> t.node[TrueLit], t >> t.node[FalseLit]) |-> { case (o:Or, c) => Or(o.left, c.head)() }
  t.node[Or]

}
