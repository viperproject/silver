// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility.rewriter

import scala.reflect.runtime.{universe => reflection}

/**
  * Extension of the Strategy context. Encapsulates all the required information for the rewriting
 *
  * @param aList       List of all the ancestors
  * @param c           context information
  * @param transformer current transformer
  * @param upContext   Function that describes how we update the context in case new context information comes in
  * @param comb Function that evaluates which context to take in case a node is in two possible contexts at the same time (true = first param, false = second param)
  * @tparam N Type of all AST nodes
  * @tparam COLL Type of custom context
  */
class RegexContext[N <: Rewritable, COLL](aList: Seq[N], val c: COLL, transformer: StrategyInterface[N], private val upContext: (COLL, COLL) => COLL, val comb: (COLL, COLL) => COLL) extends ContextA[N](aList, transformer) {

  // Add an ancestor
  override def addAncestor(n: N): RegexContext[N, COLL] = {
    new RegexContext(ancestorList ++ Seq(n), c, transformer, upContext, comb)
  }

  // Replace the current node
  override def replaceNode(n: N): RegexContext[N, COLL] = {
    new RegexContext(ancestorList.dropRight(1) ++ Seq(n), c, transformer, upContext, comb)
  }

  // Update the context with new information
  def update(con: COLL): RegexContext[N, COLL] = {
    new RegexContext(ancestorList, upContext(c, con), transformer, upContext, comb)
  }

  // Compare the context in order decide which one to take
  def combinate(other: RegexContext[N, COLL]): RegexContext[N, COLL] = {
    new RegexContext(aList, comb(this.c, other.c), transformer, upContext, comb)
  }
}

/**
  * A class that misses some information in order to be a full RegexContext. Provides methods to create a complete one
  * @param c Custom context
  * @param upContext Function that describes how we update the context in case new context information comes in
  * @param comb Function that evaluates which context to take in case a node is in two possible contexts at the same time (true = first param, false = second param)
  * @tparam N Common supertype of every node in the tree
  * @tparam COLL Type of custom context
  */
class PartialContextR[N <: Rewritable, COLL](val c: COLL, val upContext: (COLL, COLL) => COLL, val comb: (COLL, COLL) => COLL) extends PartialContext[N, ContextA[N]] {

  /**
    * Complete the Partial context by providing the missing information for a RegexContext
    * @param anc List of ancestors
    * @param transformer current transformer
    * @return complete RegexContext object
    */
  def get(anc: Seq[N], transformer: StrategyInterface[N]): RegexContext[N, COLL] = new RegexContext[N, COLL](anc, c, transformer, upContext, comb)

  /**
    * Provide the transformer for the real context
    * @param transformer current transformer
    * @return A complete Context object
    */
  override def get(transformer: StrategyInterface[N]): RegexContext[N, COLL] = new RegexContext[N, COLL](Seq(), c, transformer, upContext, comb)
}

/**
  * A class that helps with providing dummy context in a rewriting function. Used to make SlimRegexStrategy compatible with RegexStrategy
  * @param p Partial function that describes the rewriting
  * @tparam N Common supertype of every node in the tree
  */
case class SimpleRegexContext[N <: Rewritable](p: PartialFunction[N, N]) extends PartialFunction[(N, RegexContext[N, Any]), N] {
  override def isDefinedAt(x: (N, RegexContext[N, Any])): Boolean = p.isDefinedAt(x._1)

  override def apply(x: (N, RegexContext[N, Any])): N = p.apply(x._1)
}

/**
  * A regex strategy that does not include context (convenience)
  * @param a Matching regex converted into an automaton
  * @param p Partial function used for rewriting
  * @tparam N Common supertype of every node in the tree
  */
class SlimRegexStrategy[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag](a: TRegexAutomaton, p: PartialFunction[N, N]) extends RegexStrategy[N, Any](a, SimpleRegexContext(p), new PartialContextR(null, (x, y) => x, (x, y) => true))

/**
  * A strategy that performs rewriting according to the Regex and Rewriting function specified
  * @param a The automaton generated from the regular expression
  * @param p PartialFunction that describes rewriting
  * @param default The context we start with
  * @tparam N Common supertype of every node in the tree
  * @tparam COLL Type of custom context
  */
class RegexStrategy[N <: Rewritable : reflection.TypeTag : scala.reflect.ClassTag, COLL](a: TRegexAutomaton, p: PartialFunction[(N, RegexContext[N, COLL]), N], default: PartialContextR[N, COLL]) extends Strategy[N, RegexContext[N, COLL]](p) {

  type CTXT = RegexContext[N, COLL]

  // Custom data structure for keeping the node context pairs
  class MatchSet {
    var map = collection.mutable.ListBuffer.empty[(N, CTXT, Int)]

    // Put a new tuple into the data structure. If an entry for the node already exists keep the tuple with bigger context according to the regex context
    def put(tuple: (N, CTXT)) = {
      val node = tuple._1
      val context = tuple._2
      // Check if we have this node already in the list. NOTE: A node is different from an other node if the node itself differs Or one of the ancestors differs (sharing)
      val matchingNodes = map.zipWithIndex.filter( _._1._1 eq node )

      if(matchingNodes.isEmpty)
        // We don't have it already. Insert it as first node seen (index 0)
        map.append((node, context, 0))
      else {
        val exactlyMatchingNodes = matchingNodes.filter( elem => cmpAncs(elem._1._2.ancestorList, context.ancestorList ))
        exactlyMatchingNodes.length match {
          case 0 => map.append((node, context, matchingNodes.length))
          case 1 =>
            val tup = exactlyMatchingNodes.head // Got only 1 element
            val better:(N, CTXT, Int) = (node, tup._1._2.combinate(context), tup._1._3)
            map.remove(tup._2)
            map.append(better)
          case _ => throw new AssertionError("Multiple entries for same node: " + node)
        }
      }

    }
    // Get the tuple that matches parameter node
    def get(node: N, ancList:Seq[N]): Option[CTXT] = {
      // Get all matching nodes together with their index (only way to delete them later)
      val candidates = map.zipWithIndex.filter( _._1._1 eq node )

      if(candidates.isEmpty)
        // No match found
        None
      else {
        // Found a match. Make sure to get the minimum index (next in traversal order) and delete it such that the next index will be the minimum
        val mini = candidates.min(Ordering.by((t:((N, CTXT, Int), Int)) => t._1._3))
        map.remove(mini._2)
        Some(mini._1._2)
      }
    }

    // Compare two ancestor lists for equality
    def cmpAncs(s1: Seq[N], s2: Seq[N]): Boolean = s1.zip(s2).forall(nodes => nodes._1 eq nodes._2)
  }

  /**
    * Execute the rewriting specified by the regular expression
    * @param node Root of the NST you want to rewrite
    * @tparam T Type of the rewritten root
    * @return rewritten root
    */
  override def execute[T <: N](node: N): T = {
    changed = false

    // Store found matches here
    val matches = new MatchSet

    // Recursively matches on the AST by iterating through the automaton
    def recurse(n: N, s: State, ctxt: CTXT, marked: Seq[(N, CTXT)]): Unit = {

      // Perform possible transition and obtain actions.
      // If no transition is possible (error state) states will be empty after this call and the recursion will stop
      val (states, action) = s.performTransition(n)

      // Get all the children to recurse further
      val children: Seq[Rewritable] = n.children.foldLeft(Seq.empty[Rewritable])({
        case (seq, o: Option[Rewritable @unchecked]) => o match {
          case None => seq
          case Some(x: Rewritable) => seq ++ Seq(x)
        }
        case (seq, s: Seq[Rewritable @unchecked]) => seq ++ s
        case (seq, r: Rewritable) => seq ++ Seq(r)
        case (seq, _) => seq
      })

      // Actions may or may not change marked nodes, children or context
      var newMarked = marked
      val newChildren = children
      var newCtxt = ctxt.addAncestor(n)

      // Apply actions
      action foreach {
        // Marked for rewrite
        case MarkedForRewrite() => newMarked = newMarked ++ Seq((n.asInstanceOf[N], newCtxt))
        // Context update
        case ContextInfo(c: Any) => newCtxt = newCtxt.update(c.asInstanceOf[COLL]) /* TODO: This cast is *not* guaranteed to succeed! */
        // Only recurse if we are the selected child
        case ChildSelectInfo(r: Rewritable) => newChildren.filter(_ eq r)
      }

      // If we reach an accepting state put it into matches
      if (states.exists(_.isAccepting)) {
        newMarked.foreach(matches.put)
      }


      // Perform further recursion for each child and for each state that is not already accepting
      newChildren.foreach(child => {
        states.filter( s1 => !s1.isAccepting).foreach(state => {
          recurse(child.asInstanceOf[N], state, newCtxt, newMarked)
        })
      })
    }

    // Use the recurse function to find every sub patch that satisfied the regular expression and fill variable matches with all the nodes marked for rewriting

    // Efficiency: Only start if the first match matches
    val startStates = a.start.effective
    val visitor = StrategyBuilder.Ancestor[N]({ case (n, c) =>
      // Start recursion if any of the start states is valid for recursion
      startStates.foreach(s => {
        if (s.isValidInput(n))
          recurse(n, s, default.get(c.ancestorList.dropRight(1), this), Seq.empty[(N, CTXT)])
      })
      n
    })

    visitor.execute(node)

    val result = replaceTopDown(node, matches, Seq())
    changed = result != node
    result.asInstanceOf[T]
  }

  // Replace the marked nodes with the transformed nodes
  def replaceTopDown[A](node: A, matches: MatchSet, ancList: Seq[A]): A = {
    if (noRecursion.contains(node))
      node
    else {
      node match {
        case map: Map[_, _] => map.map(replaceTopDown(_, matches, ancList)).asInstanceOf[A]

        case collection: Iterable[_] => collection.map(replaceTopDown(_, matches, ancList)).asInstanceOf[A]

        case Some(value) => Some(replaceTopDown(value, matches, ancList)).asInstanceOf[A]

        case n: N => {
          val newAncList = ancList ++ Seq(n)

          // Find out if this node is going to be replaced
          val replaceInfo = matches.get(n, newAncList.asInstanceOf[Seq[N]])

          // get resulting node from rewriting
          val resultNodeO = replaceInfo match {
            case None => None
            case Some(elem) =>
              if (p.isDefinedAt(n, elem))
                Some(p(n, elem))
              else
                None
          }

          val newNode = resultNodeO.getOrElse(n)

          if (noRecursion.contains(newNode))
            newNode.asInstanceOf[A]
          else {
            val allowedToRecurse = recursionFunc.applyOrElse(newNode, (_: N) => newNode.children).toSet
            val children = newNode.children.map(child => if (allowedToRecurse(child)) replaceTopDown(child, matches, newAncList) else child)

            (newNode.children = children).asInstanceOf[A]
          }
        }

        case value => value
      }
    }
  }
}
