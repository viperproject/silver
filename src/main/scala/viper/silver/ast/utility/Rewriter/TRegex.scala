package viper.silver.ast.utility.Rewriter

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import scala.language.implicitConversions
import scala.reflect.api
import scala.reflect.runtime.universe._


/**
  * Base trait of the matching AST. Contains functions used for the DSL and creates the Regex Syntax Tree.
  */
trait Match {

  /**
    * Create a finite automaton out of this matcher
    *
    * @return The generated automaton
    */
  def createAutomaton(): TRegexAutomaton

  // Basic operators

  // Appends one match to the other
  def >(m: Match) = new Nested(this, m)

  // Conditional between two matches
  def |(m: Match) = new OrMatch(this, m)

  // 0 or 1 occurences of the match
  def ? = new Questionmark(this)

  // O or more occurences of the match (directly after each other)
  def * = new Star(this)

  // Second level operators (can be expressed with basic operators)

  // 1 or more occurences of the match (directly after each other)
  def + = this > this.*

  // Match occurs arbitrarily deep down a tree
  def >>(m: Match) = this > n.Wildcard.* > m

  // 0 or more occurences of the match (not necessarily directly after each other)
  def ** = (this.* > n.Wildcard.*).*
}


// Following classes instantiate the Match trait and provide different matches


// NMatch is the basis of all node matches. It matches on all nodes that are a subclass of N and where predicate pred holds
// If flag rewrite is set, the matched node is marked for rewriting
class NMatch[N <: Rewritable : TypeTag](val pred: N => Boolean, val rewrite: Boolean) extends Match {

  // Checks if node n (of type T) is a valid subtype of generic parameter N
  protected def matches[T: TypeTag](n: T): Boolean = {
    // TODO: This code works but im not really familiar with reflection. Is there a better solution?
    val mirror = runtimeMirror(n.getClass.getClassLoader) // obtain runtime mirror
    val sym = mirror.staticClass(n.getClass.getName) // obtain class symbol for `n`
    val tpe = sym.selfType // obtain type object for `n`

    // create a type tag which contains above type object
    val t1 = TypeTag(mirror, new api.TypeCreator {
      def apply[U <: api.Universe with Singleton](m: api.Mirror[U]) =
        if (m eq mirror) tpe.asInstanceOf[U#Type]
        else throw new IllegalArgumentException(s"Type tag defined in $mirror cannot be migrated to other mirrors.")
    }).tpe


    val t2 = typeOf[N]
    val bres = t1 <:< t2
    bres
  }


  // Method that checks if parameter node is a match
  def holds(node: Rewritable): Boolean = {
    if (matches(node)) {
      pred(node.asInstanceOf[N])
    } else {
      false
    }
  }

  // Create a finite automaton out of this matcher
  override def createAutomaton() = {
    val start = new State
    val end = new State

    start.setMTrans(end, this)
    new TRegexAutomaton(start, end)
  }

  // Provide information about the actions that occur if node n matches on this matcher
  def getTransitionInfo(n: Rewritable): Seq[TransitionInfo] = if (rewrite) Seq(MarkedForRewrite()) else Seq.empty[TransitionInfo]

}

// A match that provides context for the rewriter.
// Function c extracts the context from a node.
// The rest is inherited from NMatch
class ContextNMatch[N <: Rewritable : TypeTag](c: N => Any, predi: N => Boolean, rewrite: Boolean) extends NMatch[N](predi, rewrite) {

  // Provide information about the actions that occur if node n matches on this matcher
  override def getTransitionInfo(n: Rewritable) = {
    Seq(ContextInfo(c(n.asInstanceOf[N]))) ++ super.getTransitionInfo(n)
  }
}

// A match that allows to express recursion control by limiting the recursion on certain children
// Function ch extracts the selected children from a node
// Rest is inherited from NMatch
class ChildSelectNMatch[N <: Rewritable : TypeTag](ch: N => Rewritable, predi: N => Boolean, rewrite: Boolean) extends NMatch[N](predi, rewrite) {

  // Provide information about the actions that occur if node n matches on this matcher
  override def getTransitionInfo(n: Rewritable): Seq[TransitionInfo] = {
    Seq(ChildSelectInfo(ch(n.asInstanceOf[N]))) ++ super.getTransitionInfo(n)
  }
}

//Upper bound for all matches that take two matches and combine them to one
abstract class CombinatorMatch(val m1: Match, val m2: Match) extends Match

// Either m1 or m2 need to hold in order to match
class OrMatch(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {

  // Create a finite automaton out of this matcher
  override def createAutomaton(): TRegexAutomaton = {
    val a1 = m1.createAutomaton()
    val a2 = m2.createAutomaton()

    val start = new State
    val end = new State

    start.addETrans(a1.start)
    start.addETrans(a2.start)
    a1.end.addETrans(end)
    a2.end.addETrans(end)

    new TRegexAutomaton(start, end)
  }
}

// Either m1 needs to hold directly before m2 in order to match
class Nested(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {

  // Create a finite automaton out of this matcher
  override def createAutomaton(): TRegexAutomaton = {
    val a1 = m1.createAutomaton()
    val a2 = m2.createAutomaton()

    a1.end.addETrans(a2.start)
    new TRegexAutomaton(a1.start, a2.end)
  }
}

// m has to match 0 or more times in order to match
class Star(m: Match) extends Match {

  // Create a finite automaton out of this matcher
  override def createAutomaton(): TRegexAutomaton = {
    val a = m.createAutomaton()
    val out = new State

    a.start.addETrans(out)
    a.end.addETrans(a.start)

    new TRegexAutomaton(a.start, out)
  }
}

// m has to match 0 or 1 time in order to match
class Questionmark(m: Match) extends Match {

  // Create a finite automaton out of this matcher
  override def createAutomaton(): TRegexAutomaton = {
    val a = m.createAutomaton()

    val start = a.start
    val end = a.end
    start.addETrans(end)

    a
  }

}

// The follwing classes help in building a complete Regular expression strategy by allowing it to be filled incrementally with:
//  1. Regular expression 2. Rewriting function

// Encapsulates information about the nodes we rewrite and the way we gather the context
// accumulator: Describes how we put the contexts together into one object
// comparator: Imposes an ordering on the contexts => in case a node matches in two ways on two different contexts the bigger one is taken (true = first param, false = second param)
// default: The default context we start with
class TreeRegexBuilder[N <: Rewritable, COLL](val accumulator: (COLL, COLL) => COLL, val comparator: (COLL, COLL) => Boolean, default: COLL) {

  // Generates a TreeRegexBuilderWithMatch by adding the matching part to the mix
  def &>(f: Match) = new TreeRegexBuilderWithMatch[N, COLL](accumulator, comparator, f, default)
}

// Encapsulates the information of TreeRegexBuilder + matching information. Used to generate the regex strategy
class TreeRegexBuilderWithMatch[N <: Rewritable, COLL](val accumulator: (COLL, COLL) => COLL, val comparator: (COLL, COLL) => Boolean, regex: Match, default: COLL) {

  // Generate the regex strategy by adding the rewriting function into the mix
  def |->(p: PartialFunction[(N, RegexContext[N, COLL]), N]) = new RegexStrategy[N, COLL](regex.createAutomaton(), p, new PartialContextR(default, accumulator, comparator))
}

// Same as TreeRegexBuilder just without context
class SimpleRegexBuilder[N <: Rewritable]() {
  def &>(f: Match) = new SimpleRegexBuilderWithMatch[N](f)
}

// Same as TreeRegexBuilderWithMatch just without context
class SimpleRegexBuilderWithMatch[N <: Rewritable](regex: Match) {
  def |->(p: PartialFunction[N, N]) = new SlimRegexStrategy[N](regex.createAutomaton(), p)
}

// A companion object with useful factory methods to create a rewriting strategy
object TreeRegexBuilder {

  // full control of all the parameters: see TreeRegexBuilder for explanations
  def context[N <: Rewritable, COLL](accumulator: (COLL, COLL) => COLL, comparator: (COLL, COLL) => Boolean, default: COLL) = new TreeRegexBuilder[N, COLL](accumulator, comparator, default)

  // don't care about the custom context but want ancestor/sibling information
  def ancestor[N <: Rewritable] = new TreeRegexBuilder[N, Any]((x, y) => x, (x, y) => true, null)

  // don't care about context at all
  def simple[N <: Rewritable] = new SimpleRegexBuilder[N]
}


// This is the frontend of the DSL. Here we create the regular expression AST


// Node matches
object n {

  // Only a node match nothing else
  def apply[N <: Rewritable : TypeTag]() = new NMatch[N]((x: N) => true, false)

  // Node match with a predicate that needs to hold in order to match
  def P[N <: Rewritable : TypeTag](p: N => Boolean = (x: N) => true) = new NMatch[N](p, false)

  // Node match and mark the matched node for rewriting
  def r[N <: Rewritable : TypeTag]() = new NMatch[N]((x: N) => true, true)

  // Node match with a predicate that needs to hold in order to match. Mark the matched node for rewriting
  def r[N <: Rewritable : TypeTag](p: N => Boolean) = new NMatch[N](p, true)

  // This matches on every node
  def Wildcard = new NMatch[Rewritable]((x: Rewritable) => true, false)
}

// Match node and extract context information
object c {

  // In case the node matches extract context information from the node by applying function con. Only if predicate p holds
  def apply[N <: Rewritable : TypeTag](con: N => Any, p: N => Boolean = (x: N) => true) = new ContextNMatch[N](con, p, false)

  // Same as apply but in addition mark the matched node for rewriting
  def r[N <: Rewritable : TypeTag](con: N => Any, p: N => Boolean = (x: N) => true) = new ContextNMatch[N](con, p, true)
}

// Match node and select children for further recursion
object iC {

  // In case the node matches extract the children we want to recurse on. Only if predicate p holds
  def apply[N <: Rewritable : TypeTag](ch: N => Rewritable, p: N => Boolean = (x: N) => true): Match = new ChildSelectNMatch[N](ch, p, false)

  // Same as apply but in addition mark the matched node for rewriting
  def r[N <: Rewritable : TypeTag](ch: N => Rewritable, p: N => Boolean = (x: N) => true): Match = new ChildSelectNMatch[N](ch, p, true)
}