/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver

import scala.language.implicitConversions
import org.scalatest.{FunSuite, Matchers}
import ast._
import ast.utility.{Strategy, Transformer, Traverse}
import ast.If




class TreeRegexBuilder[N, C] {


  def c[NODE <: N](trafo:NODE=>C):Match[NODE, N, C] = ??? // Extract context
  def n[NODE <: N]():Match[NODE, N, C] = ??? // Node must be there
  def m[NODE <: N]():Match[NODE, N, C] = ??? // Match on this node
  def chs[NODE <: N](selector:NODE=>N):Match[NODE, N, C] = ???
  def ch[NODE <: N](s:Seq[Match[_, N, C]]):Match[NODE, N, C] = ???
  def >>[NODE <: N](m: Match[_, NODE, C]):Match[NODE, N, C] = ???
  def ?[NODE <: N]:Match[NODE, N, C] = ???


}

class Matcher[N, C] {


}

class AMatch {

}

class Match[NODE <: N, N, C] extends AMatch {
  def * = ???
  def + = ???
  def ^(i: Int) = ???

  def >>(m: Match[_ ,N, C]):Match[_, N, C] = ???


}

class nodeMatch[Node <: N, N, C] extends Match[N, C] {

}

class rewriteMatch[Node <: N, N, C] extends Match[N, C] {

}

class contextMatch[Node <: N, N, C](val acc:Node=>C) extends Match[N, C] {

}

class childrenMatch[Node <: N, N, C](selector:Node=>Seq[Match[N, C]]) {

}






class Test {
  val t = new TreeRegexBuilder[Node, Exp]()
  t.chs[Method](_.pres.head) >> t.n[Implies] >> t.ch[Or](Seq(t >> t.n[TrueLit], t >> t.n[FalseLit]))
  t.n[Or]

}
