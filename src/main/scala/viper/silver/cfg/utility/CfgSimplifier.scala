// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.cfg.utility

import viper.silver.cfg._

import scala.collection.mutable

/**
  * An object that provides a method to simplify a control flow graph.
  */
object CfgSimplifier {
  /**
    * Removes all blocks from the control flow graph that are not reachable from
    * the entry block.
    *
    * @param cfg The control flow graph.
    * @tparam C The type of the control flow graph.
    * @tparam S The type of the statements in the control flow graph.
    * @tparam E The type of the expressions in the control flow graph.
    * @return The control flow graph after the unreachable blocks were pruned.
    */
  def pruneUnreachable[C <: Cfg[S, E], S, E](cfg: C): C = {
    val entry = cfg.entry
    val exit = cfg.exit

    val queue = mutable.Queue[Block[S, E]]()

    // we use linked hash sets to preserve the insertion order of blocks and
    // edges since we want the result of the simplifier to be deterministic
    val blocks = mutable.LinkedHashSet[Block[S, E]]()
    val edges = mutable.LinkedHashSet[Edge[S, E]]()

    queue.enqueue(entry)
    blocks.add(entry)

    while (queue.nonEmpty) {
      val block = queue.dequeue()
      for (edge <- cfg.outEdges(block)) {
        edges.add(edge)
        val target = edge.target
        if (!blocks.contains(target)) {
          queue.enqueue(target)
          blocks.add(target)
        }
      }
    }

    val newExit = exit.filter(blocks.contains)
    cfg.copy(blocks.toList, edges.toList, entry, newExit).asInstanceOf[C]
  }

  /**
    * Simplifies the given control flow graph.
    *
    * Assumptions:
    * The exit block has no outgoing edges.
    *
    * @param cfg The control flow graph to simplify.
    * @return The simplified control flow graph.
    */
  def simplify[C <: Cfg[S, E], S, E](cfg: C): C = {
    val entry = cfg.entry
    val exit = cfg.exit

    val queue = mutable.Queue[Edge[S, E]]()
    val visited = mutable.Set[Block[S, E]]()

    // we use linked hash sets to preserve the insertion order of blocks and
    // edges since we want the result of the simplifier to be deterministic
    val blocks = mutable.LinkedHashSet[Block[S, E]]()
    val edges = mutable.LinkedHashSet[Edge[S, E]]()

    def enqueueBlock(block: Block[S, E]): Unit = {
      blocks.add(block)
      cfg.outEdges(block).foreach(enqueueEdge)
    }

    def enqueueEdge(edge: Edge[S, E]): Unit = {
      val target = edge.target
      if (visited.contains(target)) {
        edges.add(edge)
      } else {
        queue.enqueue(edge)
        visited.add(target)
      }
    }

    enqueueBlock(entry)

    while (queue.nonEmpty) {
      val edge = queue.dequeue
      val block = edge.target

      val joined = block match {
        case StatementBlock(stmts) if stmts.isEmpty =>
          // compute an optional in [out] edge that is defined iff there is exactly one in [out] edge
          val outEdges = cfg.outEdges(block)
          val in = if (cfg.inEdges(block).size == 1) Some(edge) else None
          val out = if (outEdges.size == 1) outEdges.headOption else None

          // try to join the in and out edge
          (in, out) match {
            case (Some(UnconditionalEdge(source, _, Kind.Normal)), Some(UnconditionalEdge(_, target, kind))) => Some(UnconditionalEdge(source, target, kind))
            case (Some(UnconditionalEdge(source, _, kind)), Some(UnconditionalEdge(_, target, Kind.Normal))) => Some(UnconditionalEdge(source, target, kind))
            case (Some(ConditionalEdge(condition, source, _, Kind.Normal)), Some(UnconditionalEdge(_, target, kind))) => Some(ConditionalEdge(condition, source, target, kind))
            case (Some(ConditionalEdge(condition, source, _, kind)), Some(UnconditionalEdge(_, target, Kind.Normal))) => Some(ConditionalEdge(condition, source, target, kind))
            case (Some(UnconditionalEdge(source, _, Kind.Normal)), Some(ConditionalEdge(condition, _, target, kind))) => Some(ConditionalEdge(condition, source, target, kind))
            case (Some(UnconditionalEdge(source, _, kind)), Some(ConditionalEdge(condition, _, target, Kind.Normal))) => Some(ConditionalEdge(condition, source, target, kind))
            case _ => None
          }
        case _ =>
          // do not join edges
          None
      }

      joined match {
        case Some(e) =>
          enqueueEdge(e)
        case None =>
          edges.add(edge)
          enqueueBlock(block)
      }
    }

    val newExit = exit.filter(blocks.contains)
    cfg.copy(blocks.toList, edges.toList, entry, newExit).asInstanceOf[C]
  }
}
