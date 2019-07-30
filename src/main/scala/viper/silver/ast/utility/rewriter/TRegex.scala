// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility.rewriter

import scala.reflect.runtime.{universe => reflection}

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

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

  /**
    * Appends one match to the other
    * @param m match
    * @return combined match
    */
  def >(m: Match) = new Nested(this, m)

  /**
    * Disjunction of two matches
    * @param m match
    * @return combined match
    */
  def |(m: Match) = new OrMatch(this, m)

  /**
    * 0 or 1 occurences of the match
    * @return enhanced match
    */
  def ? = new Questionmark(this)

  /**
    * O or more occurences of the match (directly after each other)
    * @return enhanced match
    */
  def * = new Star(this)

  // Second level operators (can be expressed with basic operators)

  /**
    * 1 or more occurences of the match (directly after each other)
    * @return combined match
    */
  def + = this > this.*

  /**
    * Match occurs arbitrarily deep down a tree
    * @param m match
    * @return combined match
    */
  def >>(m: Match) = this > n.Wildcard.* > m

  /**
    * 0 or more occurences of the match (not necessarily directly after each other)
    * @return combined match
    */
  def ** = (this.* > n.Wildcard.*).*
}


// Following classes instantiate the Match trait and provide different matches


/**
  * Class for all kinds of node matches
  * @param pred Predicate that needs to hold in order to match
  * @param rewrite Flag to indicate if we want to rewrite this node
  * @tparam N type of all AST nodes
  */
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


  /**
    * Method that checks if parameter node is a match
    * @param node node to match
    * @return true if node matches, false otherwise
    */
  def holds(node: Rewritable): Boolean = {
    if (matches(node)) {
      pred(node.asInstanceOf[N])
    } else {
      false
    }
  }

  /**
    * Create a finite automaton out of this matcher
    * @return The generated automaton
    */
  override def createAutomaton() = {
    val start = new State
    val end = new State

    start.setMTrans(end, this)
    new TRegexAutomaton(start, end)
  }

  /**
    * Provide information about the actions that occur if node n matches on this matcher
    * @param n node used for traversion
    * @return list of traversion infos
    */
  def getTransitionInfo(n: Rewritable): Seq[TransitionInfo] = if (rewrite) Seq(MarkedForRewrite()) else Seq.empty[TransitionInfo]

}

/**
  * A match that provides context for the rewriter
  * @param c Extracts context from the node
  * @param predi Predicate that needs to hold in order to match
  * @param rewrite Flag to indicate if we want to rewrite this node
  * @tparam N type of all AST nodes
  */
class ContextNMatch[N <: Rewritable : TypeTag](c: N => Any, predi: N => Boolean, rewrite: Boolean) extends NMatch[N](predi, rewrite) {

  // Provide information about the actions that occur if node n matches on this matcher
  override def getTransitionInfo(n: Rewritable) = {
    Seq(ContextInfo(c(n.asInstanceOf[N]))) ++ super.getTransitionInfo(n)
  }
}

/**
  * A match that allows to express recursion control by limiting the recursion on certain children
  * @param ch Extracts children from the node
  * @param predi Predicate that needs to hold in order to match
  * @param rewrite Flag to indicate if we want to rewrite this node
  * @tparam N type of all AST nodes
  */
class ChildSelectNMatch[N <: Rewritable : TypeTag](ch: N => Rewritable, predi: N => Boolean, rewrite: Boolean) extends NMatch[N](predi, rewrite) {

  // Provide information about the actions that occur if node n matches on this matcher
  override def getTransitionInfo(n: Rewritable): Seq[TransitionInfo] = {
    Seq(ChildSelectInfo(ch(n.asInstanceOf[N]))) ++ super.getTransitionInfo(n)
  }
}

/**
  * Upper bound for all matches that take two matches and combine them to one
  * @param m1 match 1
  * @param m2 match 2
  */
abstract class CombinatorMatch(val m1: Match, val m2: Match) extends Match

/**
  * Either match 1 or match 2 need to hold in order to match
  * @param m1 match1
  * @param m2 match2
  */
class OrMatch(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {

  /**
    * Create a finite automaton out of this matcher
    * @return The generated automaton
    */
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

/**
  * Either match 1 needs to hold directly before match 2 in order to match
  * @param m1 match 1
  * @param m2 match 2
  */
class Nested(m1: Match, m2: Match) extends CombinatorMatch(m1, m2) {

  /**
    * Create a finite automaton out of this matcher
    * @return The generated automaton
    */
  override def createAutomaton(): TRegexAutomaton = {
    val a1 = m1.createAutomaton()
    val a2 = m2.createAutomaton()

    a1.end.addETrans(a2.start)
    new TRegexAutomaton(a1.start, a2.end)
  }
}

/**
  * m has to match 0 or more times in order to match
  * @param m match
  */
class Star(m: Match) extends Match {

  /**
    * Create a finite automaton out of this matcher
    * @return The generated automaton
    */
  override def createAutomaton(): TRegexAutomaton = {
    val a = m.createAutomaton()
    val out = new State

    a.start.addETrans(out)
    a.end.addETrans(a.start)

    new TRegexAutomaton(a.start, out)
  }
}

/**
  * m has to match 0 or 1 time in order to match
  * @param m match
  */
class Questionmark(m: Match) extends Match {

  /**
    * Create a finite automaton out of this matcher
    * @return The generated automaton
    */
  override def createAutomaton(): TRegexAutomaton = {
    val a = m.createAutomaton()

    val start = a.start
    val end = a.end
    start.addETrans(end)

    a
  }

}

/**
  * Helps in building a complete Regular expression strategy by allowing it to be filled incrementally with: 1. Regular expression 2. Rewriting function
  * @param accumulator Describes how we put the contexts together into one object
  * @param combinator Imposes an ordering on the contexts => in case a node matches in two ways on two different contexts the bigger one is taken (true = first param, false = second param)
  * @param default The default context we start with
  * @tparam N Type of the AST
  * @tparam COLL Type of the context
  */
class TreeRegexBuilder[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag, COLL](val accumulator: (COLL, COLL) => COLL, val combinator: (COLL, COLL) => COLL, val default: COLL) {

  /**
    * Generates a TreeRegexBuilderWithMatch by adding the matching part to the mix
    * @param m Regular expression
    * @return TregexBuilderWithMatch that contains regex `f`
    */
  def &>(m: Match) = new TreeRegexBuilderWithMatch[N, COLL](this, m)
}

/**
  * Encapsulates the information of TreeRegexBuilder + matching information. Used to generate the regex strategy
  * @param tbuilder Tree regex builder
  * @param regex Regular expression used for matching
  * @tparam N Type of the AST
  * @tparam COLL Type of the context
  */
class TreeRegexBuilderWithMatch[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag, COLL](tbuilder: TreeRegexBuilder[N, COLL], regex: Match) {

  /**
    * Generate the regex strategy by adding the rewriting function into the mix
    * @param p partial function used for rewriting
    * @return complete RegexStrategy
    */
  def |->(p: PartialFunction[(N, RegexContext[N, COLL]), N]) = new RegexStrategy[N, COLL](regex.createAutomaton(), p, new PartialContextR(tbuilder.default, tbuilder.accumulator, tbuilder.combinator))
}

/**
  * Same as TreeRegexBuilder just without context
  * @tparam N Type of all AST nodes
  */
class SimpleRegexBuilder[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag]() {

  /**
    * Generates a TreeRegexBuilderWithMatch by adding the matching part to the mix
    * @param f Regular expression
    * @return SimpleTregexBuilderWithMatch that contains regex `f`
    */
  def &>(f: Match) = new SimpleRegexBuilderWithMatch[N](f)
}

/**
  * Same as TreeRegexBuilderWithMatch just without context
  * @param regex Regular expression used for matching
  * @tparam N Type of all AST nodes
  */
class SimpleRegexBuilderWithMatch[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag](regex: Match) {

  /**
    * Generate the regex strategy by adding the rewriting function into the mix
    * @param p partial function used for rewriting
    * @return complete SlimRegexStrategy
    */
  def |->(p: PartialFunction[N, N]) = new SlimRegexStrategy[N](regex.createAutomaton(), p)
}

/**
  * A companion object with useful factory methods to create a rewriting strategy
  */
object TreeRegexBuilder {

  /**
    * Constructs a TreeRegexBuilder
    * @param accumulator Describes how we put the contexts together into one object
    * @param combinator Imposes an ordering on the contexts => in case a node matches in two ways on two different contexts merge it together
    * @param default The default context we start with
    * @tparam N Type of the AST
    * @tparam COLL Type of the context
    * @return
    */
  def context[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag, COLL](accumulator: (COLL, COLL) => COLL, combinator: (COLL, COLL) => COLL, default: COLL) = new TreeRegexBuilder[N, COLL](accumulator, combinator, default)

  /**
    * Don't care about the custom context but want ancestor/sibling information
    * @tparam N Type of the AST
    * @return TreeRegexBuilder object
    */
  def ancestor[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag] = new TreeRegexBuilder[N, Any]((x, y) => x, (x, y) => true, null)

  /**
    * Don't care about context at all
    * @tparam N Type of the AST
    * @return SimpleRegexBuilder
    */
  def simple[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag] = new SimpleRegexBuilder[N]
}


// This is the frontend of the DSL. Here we create the regular expression AST


/**
  * Object to generate Simple Node matches
  */
object n {

  /**
    * Only a node match nothing else
    * @tparam N Type of the AST
    * @return Node Match
    */
  def apply[N <: Rewritable : TypeTag] = new NMatch[N]((x: N) => true, false)

  /**
    * Node match with a predicate that needs to hold in order to match
    * @param p Predicate for matching
    * @tparam N Type of the AST
    * @return Node match with predicate
    */
  def P[N <: Rewritable : TypeTag](p: N => Boolean = (x: N) => true) = new NMatch[N](p, false)

  /**
    * Node match and mark the matched node for rewriting
    * @tparam N Type of the AST
    * @return Node match marked for rewriting
    */
  def r[N <: Rewritable : TypeTag] = new NMatch[N]((x: N) => true, true)

  /**
    * Node match with a predicate that needs to hold in order to match. Mark the matched node for rewriting
    * @param p Predicate for matching
    * @tparam N Type of the AST
    * @return Node match with predicate marked for rewriting
    */
  def r[N <: Rewritable : TypeTag](p: N => Boolean) = new NMatch[N](p, true)

  /**
    * @return Convenient matcher that matches on every node
    */
  def Wildcard = new NMatch[Rewritable]((x: Rewritable) => true, false)
}

/**
  * Object to generate matches that provide context
  */
object c {

  /**
    * In case the node matches extract context information from the node by applying function con. Only if predicate p holds
    * @param con Context extractor
    * @param p Predicate for matching
    * @tparam N Type of the AST
    * @return Context match
    */
  def apply[N <: Rewritable : TypeTag](con: N => Any, p: N => Boolean = (x: N) => true) = new ContextNMatch[N](con, p, false)

  /**
    * In case the node matches extract context information from the node by applying function con and mark the node for rewriting. Only if predicate p holds
    * @param con Context extractor
    * @param p Predicate for matching
    * @tparam N Type of the AST
    * @return Context match
    */
  def r[N <: Rewritable : TypeTag](con: N => Any, p: N => Boolean = (x: N) => true) = new ContextNMatch[N](con, p, true)
}

/**
  * Object to generate node matches that select children for further recursion
  */
object iC {

  /**
    * In case the node matches extract the children we want to recurse on. Only if predicate `p` holds
    * @param ch Child extractor
    * @param p Predicate for matching
    * @tparam N Type of the AST
    * @return Children Match
    */
  def apply[N <: Rewritable : TypeTag](ch: N => Rewritable, p: N => Boolean = (x: N) => true): Match = new ChildSelectNMatch[N](ch, p, false)

  /**
    * In case the node matches extract the children we want to recurse on and mark the node for rewriting. Only if predicate `p` holds
    * @param ch Child extractor
    * @param p Predicate for matching
    * @tparam N Type of the AST
    * @return Children Match
    */
  def r[N <: Rewritable : TypeTag](ch: N => Rewritable, p: N => Boolean = (x: N) => true): Match = new ChildSelectNMatch[N](ch, p, true)
}