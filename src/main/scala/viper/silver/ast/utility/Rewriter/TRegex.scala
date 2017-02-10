package viper.silver.ast.utility.Rewriter

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import viper.silver.ast._
import viper.silver.ast.utility._

import scala.language.implicitConversions
import scala.reflect.runtime.universe._


// Core of the Regex AST
trait Match {
  def createAutomaton(): TRegexAutomaton
}

// Matches on nodes directly
class NMatch[N <: Rewritable : TypeTag](val pred: N => Boolean, val rewrite: Boolean) extends Match {
  def matches[T: TypeTag](n: T) =
    typeOf[T] <:< typeOf[N]

  def holds(node: Rewritable): Boolean = {
    if (matches(node)) {
      pred(node.asInstanceOf[N])
    } else {
      false
    }
  }

  override def createAutomaton() = {
    val start = new MatchState()
    val end = new EpsilonState()

    start.toMatch(end, this)

    new TRegexAutomaton(start, end)
  }

  def getTransitionInfo(n: Rewritable): TransitionInfo = NoTransInfo()

}

class ContextNMatch[N <: Rewritable : TypeTag](c: N => Any, predi: N => Boolean, rewrite: Boolean) extends NMatch[N](predi, rewrite) {

  override def getTransitionInfo(n: Rewritable) = {
    ContextInfo(c(n.asInstanceOf[N]))
  }
}

class ChildSelectNMatch[N <: Rewritable : TypeTag](ch: N => Rewritable, predi: N => Boolean, rewrite: Boolean) extends NMatch[N](predi, rewrite) {

  override def getTransitionInfo(n: Rewritable): TransitionInfo = {
    ChildSelectInfo(ch(n.asInstanceOf[N]))
  }
}

// Combine node matches together
abstract class CombinatorMatch(val m1: Match, val m2: Match) extends Match

class OrMatch(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {
  override def createAutomaton(): TRegexAutomaton = {
    val a1 = m1.createAutomaton()
    val a2 = m2.createAutomaton()

    val start = new EpsilonState
    val end = new EpsilonState

    start.to(a1.start)
    start.to(a2.start)
    a1.end.to(end)
    a2.end.to(end)

    new TRegexAutomaton(start, end)
  }
}

class Nested(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {
  override def createAutomaton(): TRegexAutomaton = {
    val a1 = m1.createAutomaton()
    val a2 = m2.createAutomaton()

    a1.end.to(a2.start)
    new TRegexAutomaton(a1.start, a2.end)
  }
}

class Star(m: Match) extends Match {
  override def createAutomaton(): TRegexAutomaton = {
    val a = m.createAutomaton()
    val out = new EpsilonState

    a.start.to(out)
    a.end.to(a.start)

    a
  }
}

class Questionmark(m: Match) extends Match {
  override def createAutomaton(): TRegexAutomaton = {
    val a = m.createAutomaton()

    val start = a.start
    val end = a.end
    start.to(end)

    a
  }

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

  def |->[N <: Rewritable : TypeTag](p: PartialFunction[N, N]) = ???

  def |->[N <: Rewritable : TypeTag, C](p: PartialFunction[(N, Seq[C]), N]) = new RegexStrategy[N, C](getAST.createAutomaton(), p)


}


// Simple node match
case class n[N <: Rewritable : TypeTag]() extends FrontendRegex {
  override def getAST: Match = new NMatch[N](_ => true, false)
}

// Match node in case predicate holds
case class nP[N <: Rewritable : TypeTag](predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new NMatch[N](predicate, true)
}

// Match node and mark rewritable
case class r[N <: Rewritable : TypeTag]() extends FrontendRegex {
  override def getAST: Match = new NMatch[N](_ => true, true)
}

// Match node and mark rewritable in case predicate holds
case class rP[N <: Rewritable : TypeTag](predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new NMatch[N](predicate, true)
}


// match context
case class c[N <: Rewritable : TypeTag](con: N => Any) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, _ => true, false)
}

// match context and mark node for rewriting
case class cr[N <: Rewritable : TypeTag](con: N => Any) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, _ => true, true)
}

// match context in case predicate holds
case class cP[N <: Rewritable : TypeTag](con: N => Any, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, predicate, false)
}

// match context in case predicate holds and mark node for rewriting
case class cPr[N <: Rewritable : TypeTag](con: N => Any, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ContextNMatch[N](con, predicate, true)
}

// match node and select the child for futher recursion
case class inCh[N <: Rewritable : TypeTag](ch: N => Rewritable) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, _ => true, false)
}

// match node and select the child for futher recursion and mark as rewritable
case class iCr[N <: Rewritable : TypeTag](ch: N => Rewritable) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, _ => true, true)
}

// match node in case predicate holds and select the child for futher recursion
case class inChP[N <: Rewritable : TypeTag](ch: N => Rewritable, predicate: N => Boolean) extends FrontendRegex {
  override def getAST: Match = new ChildSelectNMatch[N](ch, predicate, false)
}

// match node in case predicate holds and select the child for futher recursion and mark as rewritable
case class inChPr[N <: Rewritable : TypeTag](ch: N => Rewritable, predicate: N => Boolean) extends FrontendRegex {
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


class RegexStrategy[N <: Rewritable, C](a: TRegexAutomaton, p: PartialFunction[(N, Seq[C]), N]) extends StrategyInterface[N] {


  override def execute[T <: N](node: N): T = {
    // Find matches
    val matches = collection.mutable.ListBuffer.empty[(N, Seq[C])]

    // Recursively matches on the AST by iterating through the automaton
    def recurse(n: Rewritable, s:State, ctxt:Seq[C],  marked:Seq[(N, Seq[C])]): Unit = {

      // Base case: if we reach accepting state we matched and can add all marked nodes to the list
      if(s.isAccepting) {
        marked.foreach( matches.append(_) )
      }

      // Perform transition and corresponding actions
      val (states, action) = s.performTransition()

      val children: Seq[Rewritable] = n.getChildren.foldLeft( Seq.empty[Rewritable] )({
        case (seq, o: Option[Rewritable]) => o match {
          case None => seq
          case Some(x: Rewritable) => seq ++ Seq(x)
        }
        case (seq, s: Seq[Rewritable]) => seq ++ s
        case (seq, r: Rewritable) => seq ++ Seq(r)
        case (seq, _) => seq
      })

      children.foreach( child => {
        states.foreach( state => {
          // TODO make this a list and perform all actions
          action match {
            // Marked for rewrite
            case MarkedForRewrite() => recurse(child, state, ctxt, marked ++ Seq((node, ctxt)) )
            // Context update
            case ContextInfo(c:Any) => recurse(child, state, ctxt ++ Seq(c.asInstanceOf[C]), marked)
            // Only recurse if we are the selected child
            case ChildSelectInfo(r:Rewritable) => if(r eq child) recurse(child, state, ctxt, marked)
            // Nothing special just recurse further
            case NoTransInfo() => recurse(child, state, ctxt, marked)
          }
        })
      })
    }




    // Replace matches with product nodes
    val replacer = StrategyBuilder.SlimStrategy[N]({
      case n =>
        // Get node context pair and the index of it
        val replaceInfo = matches.zipWithIndex.find(_._1._1 eq n)
        replaceInfo match {
          case None => n
          case Some(elem) =>
            // Extract the information into more readable variable names
            val index = elem._2
            val node = elem._1._1
            val context = elem._1._2

            // Remove the element from the list buffer (if we don't do this we run into problem with multiple matches on the same node)
            matches.remove(elem._2)

            // Produce new version of the node
            p(node, context)
        }
    })
    val result = replacer.execute[T](node)
    result
  }

}