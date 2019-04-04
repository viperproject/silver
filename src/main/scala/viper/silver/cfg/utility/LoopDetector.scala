// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

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

    if (!isReducible(cfg, dominators))
      throw new IllegalArgumentException("Control flow graph is not reducible.")

    for (edge <- cfg.edges if dominators.isBackedge(edge)) {
      val head = edge.target
      val blocks = collectBlocks(cfg, edge)
      //blocks.map(loops).foreach(_.add(head))t
      for (block <- blocks) {
        val updated = allLoops(block) + head
        allLoops.put(block, updated)
      }
    }

    val queue = mutable.Queue[Block[S, E]]()
    val heads = mutable.Map[Block[S, E], Block[S, E]]()
    // we use linked hash sets to preserve the insertion order of blocks and
    // edges since we want the result of the loop detector to be deterministic
    val blocks = mutable.LinkedHashSet[Block[S, E]]()
    val edges = mutable.LinkedHashSet[Edge[S, E]]()

    val entry = cfg.entry
    val exit = cfg.exit

    queue.enqueue(entry)
    blocks.add(entry)

    while (queue.nonEmpty) {
      // Note: In case a block has been turned into a loop head, this is still
      // the original block.
      val block = queue.dequeue()

      for (edge <- cfg.outEdges(block)) {
        val before = allLoops(edge.source)
        val after = allLoops(edge.target)
        val out = (before -- after).size
        val in = (after -- before).size
        val mid = Math.max(out + in - 1, 0)

        // get source
        val first = heads.getOrElse(edge.source, edge.source)
        // turn target into loop head if edge is an in-edge
        val last = if (0 < in && out == 0) edge.target match {
          case head@LoopHeadBlock(_, _) => head
          case block@StatementBlock(stmts) =>
            val head: Block[S, E] = LoopHeadBlock(stmts = stmts)
            heads.put(block, head)
            head
          case ConstrainingBlock(_, _) => ??? // TODO:
          case _ => ??? // We don't expect this to happen.
        } else heads.getOrElse(edge.target, edge.target)

        if (mid == 0) {
          // update edge
          val kind = if (out > 0) Kind.Out else if (in > 0) Kind.In else Kind.Normal
          val updated = edge match {
            case UnconditionalEdge(_, _, _) => UnconditionalEdge(first, last, kind)
            case ConditionalEdge(condition, _, _, _) => ConditionalEdge(condition, first, last, kind)
          }
          edges.add(updated)
        } else {
          // set source and condition for the first edge
          var source = first
          var condition = edge match {
            case ConditionalEdge(c, _, _, _) => Some(c)
            case _ => None
          }
          // create edges and intermediate blocks
          for (index <- 0 to mid) {
            // set target and kind of current edge
            val target = if (index == mid) last else {
              val intermediate: Block[S, E] = if (index < in) LoopHeadBlock() else StatementBlock()
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

        if (!blocks.contains(last)) {
          queue.enqueue(edge.target)
          blocks.add(last)
        }
      }
    }

    cfg.copy(blocks.toList, edges.toList, entry, exit).asInstanceOf[C]
  }

  def isReducible[S, E](cfg: Cfg[S, E]): Boolean =
    isReducible(cfg, Dominators(cfg))

  def isReducible[S, E](cfg: Cfg[S, E], dominators: Dominators[S, E]): Boolean = {

    val n = cfg.blocks.size
    val indices = mutable.Map[Block[S, E], Int]()
    val low = Array.range(0, n)

    def dfs(block: Block[S, E], index: Int = 0): (Int, Boolean) = {
      indices.put(block, index)
      val edges = cfg.outEdges(block)
      val (lastIndex, lastLow, lastReducible) = edges.foldLeft((index, index, true)) {
        case ((currentIndex, currentLow, currentReducible), edge) =>
          val successor = edge.target
          if (!currentReducible || dominators.isBackedge(edge)) {
            (currentIndex, currentLow, currentReducible)
          } else if (indices.contains(successor)) {
            val successorIndex = indices(successor)
            val successorLow = low(successorIndex)
            val nextLow = Math.min(currentLow, successorLow)
            (currentIndex, nextLow, currentReducible)
          } else {
            val successorIndex = currentIndex + 1
            val (nextIndex, successorReducible) = dfs(successor, successorIndex)
            val nextLow = Math.min(currentLow, low(successorIndex))
            val nextReducible = currentReducible && successorReducible
            low(successorIndex) = Int.MaxValue
            (nextIndex, nextLow, nextReducible)
          }
      }
      val reducible = index <= lastLow
      (lastIndex, lastReducible && reducible)
    }

    val (_, reducible) = dfs(cfg.entry)
    reducible
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
  def collectBlocks[S, E](cfg: Cfg[S, E], backedge: Edge[S, E]): Set[Block[S, E]] = {
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
