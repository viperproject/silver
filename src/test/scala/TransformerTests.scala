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



/*
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
*/
class ChildMatch[+N]() {

}

case class cN[N]() extends ChildMatch[N] {}
object ** extends ChildMatch
object ? extends ChildMatch

class TRegex[N <: Rewritable[N] ,C] {
  def |->(p: PartialFunction[(N, Seq[C]), N]): Strategy[N, ContextC[N, Seq[C]]] = ???
  def %(m:Match[N]): TRegex[N, C] = ???

  def >>(m: Match[N]):TRegex[N, C] = ???
  def >(m:Match[N]):TRegex[N, C] = ???

}

class Match[+N] {
  def *(): Match[N] = ???
  def +(): Match[N] = ???

  def ^(i: Int): Match[N] = ???

}

case class n[N]() extends Match[N] { }

case class r[N]() extends Match[N] { }

case class c[N](acc:N=>Any) extends Match[N] { }

case class intoChild[N](selector:N=>Node) extends Match[N] {}

case class matchChildren[N](s: ChildMatch[N]*) extends Match[N] { }

case class nP[N](p: N=>Boolean) extends Match[N] {}

object TRegex {
  def noRec[N](n: N): N = ???
}




class Test {
  //val t = new TreeRegexBuilder[Node, Exp]()
  new TRegex[Node, Exp] % intoChild[Method](_.pres.head) >> n[Implies] > matchChildren[Or](**).* >> n[Implies] |-> { case (o:Or, c) => Or(o.left, c.head)() }

}
