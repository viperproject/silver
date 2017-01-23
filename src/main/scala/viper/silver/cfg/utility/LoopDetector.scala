/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.cfg.utility

import viper.silver.cfg._

import scala.collection.mutable

/**
  * An object that provides a method to detect loops in a control flow graph.
  */
object LoopDetector {
  /**
    * Detects natural loops in a control flow graph and returns a version of the
    * control flow graph where the edges entering and leaving loops are marked
    * accordingly.
    *
    * @param cfg The control flow graph.
    * @tparam C The type of the control flow graph.
    * @tparam S The type of the statements in the control flow graph.
    * @tparam E The type of the expressions in the control flow graph.
    * @return A control flow graph where the edges entering and leaving loops
    *         are marked.
    */
  def detect[C <: Cfg[S, E], S, E](cfg: C, loops: Map[Block[S, E], Set[Block[S, E]]] = Map[Block[S, E], Set[Block[S, E]]]()): C = {

    val allLoops = mutable.Map[Block[S, E], Set[Block[S, E]]](loops.toSeq: _*).withDefault(_ => Set())
    val dominators = new Dominators(cfg)

    for (edge <- cfg.edges if dominators.isRetrieving(edge)) {
      if (dominators.isBackedge(edge)) {
        val head = edge.target
        val blocks = collectBlocks(cfg, edge)
        //blocks.map(loops).foreach(_.add(head))t
        for (block <- blocks) {
          val updated = allLoops(block) + head
          allLoops.put(block, updated)
        }
      } else {
        // TODO: Report that the control flow graph is not reducible.
      }
    }

    val queue = mutable.Queue[Block[S, E]]()
    val blocks = mutable.Set[Block[S, E]]()
    val edges = mutable.Set[Edge[S, E]]()

    val entry = cfg.entry
    val exit = cfg.exit

    queue.enqueue(entry)
    blocks.add(entry)

    while (queue.nonEmpty) {
      val block = queue.dequeue()

      for (edge <- cfg.outEdges(block)) {
        val before = allLoops(edge.source)
        val after = allLoops(edge.target)
        val out = (before -- after).size
        val in = (after -- before).size
        val mid = Math.max(out + in - 1, 0)

        if (mid == 0) {
          // update edge
          val kind = if (out > 0) Kind.Out else if (in > 0) Kind.In else Kind.Normal
          val updated = edge match {
            case UnconditionalEdge(source, target, _) => UnconditionalEdge(source, target, kind)
            case ConditionalEdge(condition, source, target, _) => ConditionalEdge(condition, source, target, kind)
          }
          edges.add(updated)
        } else {
          // set source and condition for the first edge
          var source = edge.source
          var condition = edge match {
            case ConditionalEdge(c, _, _, _) => Some(c)
            case _ => None
          }
          // create edges and intermediate blocks
          for (index <- 0 to mid) {
            // set target and kind of current edge
            val target = if (index == mid) edge.target else {
              val intermediate: Block[S, E] = StatementBlock()
              blocks.add(intermediate)
              intermediate
            }
            val kind = if (index < out) Kind.Out else Kind.asInstanceOf
            // create current edge
            val current = condition match {
              case Some(c) => ConditionalEdge(c, source, target, kind)
              case None => UnconditionalEdge(source, target, kind)
            }
            edges.add(current)
            // set source and condition for the next edge
            source = target
            condition = None
          }
        }

        if (!blocks.contains(edge.target)) {
          queue.enqueue(edge.target)
          blocks.add(edge.target)
        }
      }
    }

    cfg.copy(blocks.toList, edges.toList, entry, exit).asInstanceOf[C]
  }

  /**
    * Returns the set of edges belonging to the part of an natural loop in the
    * given control flow graph defined by the given backedge.
    *
    * @param cfg      The cfg.
    * @param backedge The backedge.
    * @tparam S The type of the statements in the control flow graph.
    * @tparam E The type of the expressions in the control flow graph.
    * @return The set of edges belonging to the part of an natural loop in the
    *         given control flow graph defined by the given backedge.
    */
  private def collectBlocks[S, E](cfg: Cfg[S, E], backedge: Edge[S, E]): Set[Block[S, E]] = {
    // initialize
    val result = mutable.Set[Block[S, E]]()
    val stack = mutable.Stack[Block[S, E]]()
    val head = backedge.target
    val first = backedge.source
    stack.push(first)
    result.add(first)
    // collect all blocks belonging to the loop
    while (stack.nonEmpty) {
      val current = stack.pop()
      if (current != head) {
        for (predecessor <- cfg.predecessors(current) if !result.contains(predecessor)) {
          stack.push(predecessor)
          result.add(predecessor)
        }
      }
    }
    // return result
    result.toSet
  }
}
