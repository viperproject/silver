package viper.silver.ast.utility

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import viper.silver.ast._

import scala.language.implicitConversions
import scala.reflect.ClassTag











// Core of the Regex AST
trait Match {
}

// Matches on nodes directly
class NMatch[N <: Rewritable : ClassTag[N]] extends Match {

}

class PredicateNMatch[N <: Rewritable : ClassTag[N]](p: N => Boolean) extends NMatch {

}

class ContextNMatch[N <: Rewritable : ClassTag[N]](c: N => Any) extends NMatch {

}

class RewriteNMatch[N <: Rewritable : ClassTag[N]] extends NMatch {

}

class ChildSelectNMatch[N <: Rewritable : ClassTag[N]](ch: N => Rewritable) extends NMatch {

}

class WildNMatch extends NMatch {

}

// Combine node matches together
class CombinatorMatch(val m1: Match, val m2: Match) extends Match {

}

class Or(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {

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

  // a >> b == a > _* > b
  def >>(m: FrontendRegex) = {
    NestedF(NestedF(this, Wild.*), m)
  }

  def >(m: FrontendRegex) = {
    new Nested(this.getAST, m.getAST)
  }

  def ?  = {
    QuestionmarkF(this)
  }

  def * = {
    StarF(this)
  }


  // a+ == a > a*
  def + = {
    PlusF(this)
  }

}

case class n[N <: Rewritable : ClassTag[N]]() extends FrontendRegex {
  override def getAST: Match = new NMatch[N]()
}

case class nP[N <: Rewritable : ClassTag[N]](p: N => Boolean ) extends FrontendRegex {
  override def getAST: Match = new PredicateNMatch[N](p)
}

case class c[N <: Rewritable : ClassTag[N]](con: N => Any) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con)
}

case class r[N <: Rewritable : ClassTag[N]]() extends FrontendRegex {
  override def getAST: Match = new RewriteNMatch[N]()
}

case class inCh[N <: Rewritable : ClassTag[N]](ch: N => Rewritable) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch)
}

object Wild extends FrontendRegex {
  override def getAST: Match = new WildNMatch()
}

case class StarF(m: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Star(m.getAST)
}


case class PlusF(m: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Nested(m.getAST, m.*.getAST)
}

case class QuestionmarkF(m: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Questionmark(m.getAST)
}

case class NestedF(m1: FrontendRegex, m2: FrontendRegex) extends FrontendRegex {
  override def getAST: Match = new Nested(m1.getAST, m2.getAST)
}

class Test {
  c[QuantifiedExp](_.variables).* >> r[Or]

}
