// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.cfg.utility

import java.util.concurrent.atomic.AtomicInteger

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{Exp, If, Info, Infoed, MakeInfoPair, Method, NoInfo, Node, Seqn, Stmt}
import viper.silver.cfg._
import viper.silver.cfg.silver.SilverCfg.{SilverBlock, SilverEdge}
import viper.silver.cfg.silver.{CfgGenerator, SilverCfg}

import scala.collection.mutable

/**
  * An info used to assign unique identifier to AST nodes.
  *
  * @param id The id of the node.
  */
case class IdInfo(id: Int) extends Info {
  override def comment: Seq[String] = Seq(s"id = $id")

  override def isCached: Boolean = false
}

case class LoopInfo(head: Option[Int], loops: Set[Int]) extends Info {
  override def comment: Seq[String] = Seq(toString)

  override def isCached: Boolean = false
}

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
    // compute natural loops and merge them with provided loop information
    val allLoops = naturalLoops[C, S, E](cfg).foldLeft(loops) {
      case (current, (key, value)) => current.updated(key, current.getOrElse(key, Set.empty) ++ value)
    }
    // augment cfg with loop information
    augment(cfg, allLoops)
  }

  def detect(method: Method): Method = method.body match {
    case Some(body) =>
      val saved = ViperStrategy.forceRewrite
      ViperStrategy.forceRewrite = true

      // extend statements in ast with ids
      val id = new AtomicInteger(0)
      val withIds = body.transform({
        case node@(_: If | _: Seqn) => node
        case node =>
          val (pos, info, err) = node.meta
          val updated = MakeInfoPair(IdInfo(id.incrementAndGet()), info)
          node.withMeta(pos, updated, err)
      }, Traverse.TopDown)

      // compute cfg and loops
      val (cfg, syntacticLoops) = CfgGenerator.computeCfg(withIds)
      val loops = naturalLoops[SilverCfg, Stmt, Exp](cfg).foldLeft(syntacticLoops) {
        case (current, (key, value)) => current.updated(key, current.getOrElse(key, Set.empty) ++ value)
      }

      def getId(stmt: Stmt): Option[Int] = stmt.info.getUniqueInfo[IdInfo].map(_.id)

      def getFirst(block: SilverBlock): Option[Stmt] = block.elements.collectFirst { case Left(s) => s }

      def getLast(block: SilverBlock): Option[Stmt] = block.elements.collect { case Left(s) => s }.lastOption

      // contract edges such that there are no empty blocks in between blocks
      val contractedEdges = cfg.blocks.flatMap { block =>
        def contract(block: SilverBlock, first: Option[SilverBlock] = None): Seq[SilverEdge] =
          if (first.contains(block)) Seq.empty
          else cfg.outEdges(block).flatMap { edge =>
            val next = edge.target
            next match {
              case StatementBlock(stmts) if stmts.isEmpty =>
                contract(next, first.orElse(Some(block))).map { nextEdge =>
                  val source = edge.source
                  val target = nextEdge.target
                  UnconditionalEdge(source, target)
                }
              case _ => Seq(edge)
            }
          }

        contract(block)
      }

      // maps blocks to ids
      val ids = cfg.blocks.foldLeft(Map.empty[SilverBlock, Int]) {
        case (map, block@LoopHeadBlock(_, _, Some(id))) => map.updated(block, id)
        case (map, block) => getFirst(block)
          .flatMap(getId)
          .map { id => map.updated(block, id) }
          .getOrElse(map)
      }

      // compute loop information
      val infos = contractedEdges.foldLeft(Map.empty[Int, LoopInfo]) {
        case (map, edge) =>
          val sourceHeads = loops.getOrElse(edge.source, Set.empty).map(ids)
          val targetHeads = loops.getOrElse(edge.target, Set.empty).map(ids)
          val outHeads = sourceHeads -- targetHeads
          val inHeads = targetHeads -- sourceHeads
          if (outHeads.isEmpty && inHeads.isEmpty) map
          else {
            // update before info
            val before = getLast(edge.source).flatMap(getId)
            val map2 = before
              .map { id =>
                val head = before.flatMap { id => map.get(id).flatMap(_.head) }
                map.updated(id, LoopInfo(head, sourceHeads))
              }
              .getOrElse(map)
            // update after info
            val after = edge.target match {
              case LoopHeadBlock(_, _, loopId) => loopId
              case block => getFirst(block).flatMap(getId)
            }
            val map3 = after
              .map { id =>
                val head = if (inHeads.nonEmpty) after else None
                map2.updated(id, LoopInfo(head, targetHeads))
              }
              .getOrElse(map2)
            // return updated map
            map3
          }
      }

      // extend ast with loop information
      val withInfo = withIds.transform({
        case node: Infoed =>
          val (pos, info, err) = node.meta
          info.getUniqueInfo[IdInfo] match {
            case Some(idInfo) =>
              val removed = info.removeUniqueInfo[IdInfo]
              val loopInfo = infos.getOrElse(idInfo.id, NoInfo)
              val updated = MakeInfoPair(removed, loopInfo)
              node.withMeta(pos, updated, err)
            case None => node
          }
        case node => node
      }, Traverse.TopDown)

      // restore forced rewriting settings
      ViperStrategy.forceRewrite = saved

      // return updated method
      method.copy(body = Some(withInfo))(method.pos, method.info, method.errT)
    case _ => method
  }

  private def naturalLoops[C <: Cfg[S, E], S, E](cfg: C): Map[Block[S, E], Set[Block[S, E]]] = {
    // check whether the control flow graph is reducible
    val dominators = new Dominators(cfg)
    if (!isReducible(cfg, dominators))
      throw new IllegalArgumentException("Control flow graph is not reducible.")

    // populate map that maps each block to the set of loop heads corresponding to all loops that contain the block
    cfg.edges
      .filter(dominators.isBackedge)
      .foldLeft[Map[Block[S, E], Set[Block[S, E]]]](Map.empty) {
      case (current, edge) =>
        val head = edge.target
        collectBlocks(cfg, edge).foldLeft(current) {
          case (c, block) =>
            val existing = c.getOrElse(block, Set.empty)
            c.updated(block, existing + head)
        }
    }
  }

  private def augment[C <: Cfg[S, E], S, E](cfg: C, loops: Map[Block[S, E], Set[Block[S, E]]]): C = {
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
        val sourceHeads = loops.getOrElse(edge.source, Set.empty)
        val targetHeads = loops.getOrElse(edge.target, Set.empty)
        val out = (sourceHeads -- targetHeads).size
        val in = (targetHeads -- sourceHeads).size
        val mid = Math.max(out + in - 1, 0)

        // get source
        val first = heads.getOrElse(edge.source, edge.source)
        // turn target into loop head if edge is an in-edge
        val last = if (0 < in && out == 0) edge.target match {
          case head@LoopHeadBlock(_, _, _) => head
          case block@StatementBlock(stmts) =>
            val loopId = stmts.head match {
              case stmt: Stmt => stmt.info.getUniqueInfo[IdInfo].map(_.id)
              case _ => None
            }
            val head: Block[S, E] = LoopHeadBlock(Seq.empty, stmts, loopId)
            heads.put(block, head)
            head
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
