/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.cfg.utility

import viper.silver.cfg.{Block, Cfg}

import scala.collection.mutable

/**
  * Provides the dominator relation of a control flow graph.
  *
  * @param cfg The control flow graph.
  * @tparam S The type of the statements in the control flow graph.
  * @tparam E The type of the expressions in the control flow graph.
  */
class Dominators[S, E](val cfg: Cfg[S, E]) {
  /**
    * Returns the immediate dominator of the given block.
    *
    * @param block The block.
    * @return The immediate dominator of the given block.
    */
  def dominator(block: Block[S, E]): Block[S, E] =
    dominators(block)

  /**
    * Returns whether the given first block dominates the given second block.
    * @param first  The first block.
    * @param second The second block.
    * @return True if and only if the given first block dominates the given
    *         second block.
    */
  def dominates(first: Block[S, E], second: Block[S, E]): Boolean =
    if (first == second) true
    else if (second == cfg.entry) false
    else dominates(first, dominators(second))

  /**
    * Returns a map representing the immediate dominator relation for the given
    * control flow graph.
    *
    * Note: The implementation assumes that the control flow graph is connected.
    *
    * Note: This implementation follows the paper "A Fast Algorithm for Finding
    * Dominators in a Flowgraph" by T. Lengauer and R. Tarjan.
    */
  private def dominators: Map[Block[S, E], Block[S, E]] = {
    // initialize and set up data structures
    val n = cfg.blocks.size
    val indices = mutable.Map[Block[S, E], Int]()
    val blocks = Array.ofDim[Block[S, E]](n)
    val parents = Array.ofDim[Int](n)
    val ancestors = Array.range(0, n)
    val label = Array.range(0, n)
    val buckets = Array.fill(n)(mutable.Set[Int]())
    val sdom = Array.ofDim[Int](n)
    val idom = Array.ofDim[Int](n)

    /**
      * Helper function for the depth first search.
      *
      * @param block The block being visited.
      * @param index The dfs number of the block being visited.
      * @return The number of the last block visited during the recursive call.
      */
    def dfs(block: Block[S, E], index: Int = 0): Int = {
      // process current block
      indices.put(block, index)
      blocks(index) = block
      sdom(index) = index
      // recursively process unvisited successors
      val successors = cfg.successors(block)
      successors.foldLeft(index) { case (current, successor) =>
        if (indices.contains(successor)) current
        else {
          val next = current + 1
          parents(next) = index
          dfs(successor, next)
        }
      }
    }

    /**
      * Helper function that links the two given nodes in the forest of
      * auxiliary trees.
      *
      * @param parent The parent node.
      * @param child  The child node.
      */
    def link(parent: Int, child: Int) = ancestors(child) = parent

    /**
      * Evaluates the the node with the smallest semi-dominator on the path
      * from the node with the given index to the root of the corresponding
      * auxiliary tree.
      *
      * @param index The index of the node.
      * @return The node with the properties described above.
      */
    def evaluate(index: Int): Int = {
      val ancestor = ancestors(index)
      if (ancestor != index) {
        // evaluate label of ancestor
        val ancestorLabel = evaluate(ancestor)
        // update label
        if (sdom(ancestorLabel) < sdom(label(index))) {
          label(index) == ancestorLabel
        }
        // compress path
        ancestors(index) = ancestors(ancestor)
      }
      label(index)
    }

    // perform depth first search
    dfs(cfg.entry)

    // compute semi-dominators and implicitly define immediate dominators
    for (index <- n - 1 until 0 by -1) {
      // compute semi-dominator
      sdom(index) = cfg
        .predecessors(blocks(index))
        .map(indices(_))
        .foldLeft(sdom(index)) { (min, pred) =>
          val evaluated = evaluate(pred)
          val candidate = sdom(evaluated)
          Math.min(min, candidate)
        }
      // update buckets
      buckets(sdom(index)).add(index)
      // update forst of auxiliary trees
      val parent = parents(index)
      link(parent, index)
      // implicitly compute immediate dominators
      val bucket = buckets(parent)
      for (v <- bucket) {
        val u = evaluate(v)
        idom(v) = if (sdom(u) < sdom(v)) u else parent
      }
      bucket.clear()
    }

    // explicitly define the immediate dominator
    for (index <- 1 until n) {
      if (idom(index) != sdom(index)) {
        idom(index) = idom(idom(index))
      }
    }

    // create map representing the immediate dominator relation
    val relation = for (index <- 0 until n) yield {
      blocks(index) -> blocks(idom(index))
    }

    relation.toMap
  }
}
