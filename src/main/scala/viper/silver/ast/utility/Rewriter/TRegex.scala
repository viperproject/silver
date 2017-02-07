package viper.silver.ast.utility.Rewriter

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import viper.silver.ast._
import viper.silver.ast.utility._

import scala.language.implicitConversions
import scala.reflect.ClassTag


// Core of the Regex AST
trait Match {
}

trait NodePredicate[T] {
  def pred:T=>Boolean

  def holds(node: T): Boolean = pred(node)
}

// Matches on nodes directly
class NMatch[N <: Rewritable : ClassTag](val pred:N=>Boolean, val rewrite:Boolean) extends Match with NodePredicate[N] {
}

class ContextNMatch[N <: Rewritable : ClassTag](c: N => Any, predi:N=>Boolean, rewrite:Boolean) extends NMatch[N](predi, rewrite) {

}

class ChildSelectNMatch[N <: Rewritable : ClassTag](ch: N => Rewritable, predi:N=>Boolean, rewrite:Boolean) extends NMatch[N](predi, rewrite) {

}

// Combine node matches together
class CombinatorMatch(val m1: Match, val m2: Match) extends Match {

}

class OrMatch(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {

}

class Nested(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {

}

// Qantify how often we macht on a node
class QuantifierMatch(m: Match) extends Match {

}

class Star(m: Match) extends Match {

}

class Questionmark(m: Match) extends Match {

}


// Frontend of the Regex AST
trait FrontendRegex {
  def getAST: Match

  def >>(m: FrontendRegex) = DeepNestedF(this, m)

  def >(m: FrontendRegex) = NestedF(this, m)

  def ? = QuestionmarkF(this)

  def * = StarF(this)

  def ** = DoubleStarF(this)

  def + = PlusF(this)

  def |(m: FrontendRegex) = OrF(this, m)

}

// Simple node match
case class n[N <: Rewritable : ClassTag]() extends FrontendRegex {
  override def getAST: Match = new NMatch[N](_ => true, false)
}

// Match node in case predicate holds
case class nP[N <: Rewritable : ClassTag](predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new NMatch[N](predicate, true)
}

// Match node and mark rewritable
case class r[N <: Rewritable : ClassTag]() extends FrontendRegex {
  override def getAST: Match = new NMatch[N](_ => true, true)
}

// Match node and mark rewritable in case predicate holds
case class rP[N <: Rewritable : ClassTag](predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new NMatch[N](predicate, true)
}


// match context
case class c[N <: Rewritable : ClassTag](con: N => Any) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, _ => true, false)
}

// match context and mark node for rewriting
case class cr[N <: Rewritable : ClassTag](con: N => Any) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, _ => true, true)
}

// match context in case predicate holds
case class cP[N <: Rewritable : ClassTag](con: N => Any, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, predicate, false)
}

// match context in case predicate holds and mark node for rewriting
case class cPr[N <: Rewritable : ClassTag](con: N => Any, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, predicate, true)
}

// match node and select the child for futher recursion
case class inCh[N <: Rewritable : ClassTag](ch: N => Rewritable) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, _ => true, false)
}

// match node and select the child for futher recursion and mark as rewritable
case class iCr[N <: Rewritable : ClassTag](ch: N => Rewritable) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, _ => true, true)
}

// match node in case predicate holds and select the child for futher recursion
case class inChP[N <: Rewritable : ClassTag](ch: N => Rewritable, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, predicate, false)
}

// match node in case predicate holds and select the child for futher recursion and mark as rewritable
case class inChPr[N <: Rewritable : ClassTag](ch: N => Rewritable, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, predicate, true)
}



case class StarF(m: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Star(m.getAST)
}

case class DoubleStarF(m: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Star(new Nested(m.*.getAST, n[Rewritable].*.getAST))
}

case class PlusF(m: FrontendRegex) extends FrontendRegex {
  // Reduction: a+ == a > a*
  override def getAST: Match = new Nested(m.getAST, m.*.getAST)
}

case class QuestionmarkF(m: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Questionmark(m.getAST)
}

case class NestedF(m1: FrontendRegex, m2: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Nested(m1.getAST, m2.getAST)
}

case class OrF(m1: FrontendRegex, m2: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new OrMatch(m1.getAST, m2.getAST)
}

case class DeepNestedF(m1: FrontendRegex, m2: FrontendRegex) extends FrontendRegex {
  // a >> b == a > _* > b
  override def getAST: Match = new Nested(new Nested(m1.getAST, n[Rewritable].*.getAST), m2.getAST)
}

class Test {
  c[QuantifiedExp](_.variables).** >> nP[Or](_.left eq TrueLit()())
}
