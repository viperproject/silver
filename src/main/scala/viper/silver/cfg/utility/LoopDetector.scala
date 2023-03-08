// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.cfg.utility

import java.util.concurrent.atomic.AtomicInteger

import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{Exp, If, Info, Infoed, LocalVar, MakeInfoPair, NoInfo, Seqn, Stmt}
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

/**
  * An info used to connect the provide loop information to AST nodes.
  *
  * @param head Contains a loop identifier i iff the node is a loop head of loop i.
  * @param loops All loops that the node is contained in.
  */
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
    val (allLoops,_) = naturalLoops[C, S, E](cfg, loops)
    /*
    allLoops.foldLeft(loops) {
      case (current, (key, value)) => current.updated(key, current.getOrElse(key, Set.empty) ++ value)
    }
    */
    // augment cfg with loop information
    augment(cfg, allLoops)
  }

  /**
    *
    * @param body The ast to analyze. Ensure that:
    *             1) The first statement of each if branch is a non-composite statement.
    *             2) The first and last statement of each while loop is a non-composite statement.
    * @param generateUniqueIds If true, then in the returned AST the info field of each non-composite node in the
    *                          returned AST contains a {@link IdInfo} object holding a unique identifier.
    * @param computeWrittenVars If true, then a map is returned from loop identifiers to corresponding written variables.
    * @return A tuple consisting of:
    *         1) An augmented version of the provided AST, where only the info fields are adjusted. For each statement s
    *         that is non-composite or a While statement, a LoopInfo object is added to the information field if the
    *         following holds:
    *         The next non-composite statement of s (or a previous non-composite statement of s) in the AST w.r.t.
    *         control flow (i.e., for a goto statement the next non-composite statement would be the corresponding label)
    *         is part of a different set of loops than s.
    *         Furthermore, unique identifiers may be added dependent on the provided parameters.
    *         2) A map from loop identifiers to corresponding written variables (depending on the provided parameters).
    */
  def detect(body: Seqn, generateUniqueIds: Boolean, computeWrittenVars: Boolean): (Seqn, Option[Map[Int, Seq[LocalVar]]]) = {
      // extend statements in ast with ids
      val id = new AtomicInteger(0)
      val withIds = body.transformForceCopy({
        case node@(_: If | _: Seqn) => node
        case node: Stmt =>
          val (pos, info, err) = node.meta
          val updated = MakeInfoPair(IdInfo(id.incrementAndGet()), info)
          node.withMeta(pos, updated, err)
        case node: Any => node
      }, Traverse.TopDown)

      // compute cfg and loops
      val (cfg, syntacticLoops) = CfgGenerator.computeCfg(withIds, true)

      val (loops, dominators) = naturalLoops[SilverCfg, Stmt, Exp](cfg, syntacticLoops)
      loops.foldLeft(syntacticLoops) {
        case (current, (key, value)) => current.updated(key, current.getOrElse(key, Set.empty) ++ value)
      }

      val writtenVars = writtenVariables(cfg, dominators)

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
        case (map, block@LoopHeadBlock(_, _, Some(id))) => {
          map.updated(block, id)
        }
        case (map, block) => getFirst(block)
          .flatMap(getId)
          .map { id => map.updated(block, id) }
          .getOrElse(map)
      }

      // associate written variables with block id
      val loopToWrittenVars =
        if(computeWrittenVars)
          Some(
            writtenVars.foldLeft(Map.empty[Int, Seq[LocalVar]]) {
              case (map, (loopHead, writtenVars)) => {
                map.updated(ids.get(loopHead).get, writtenVars.distinct)
              }
            })
        else
          None

    // compute loop information
      val infos = contractedEdges.foldLeft(Map.empty[Int, LoopInfo]) {
        case (map, edge) =>
          val sourceHeads = loops.getOrElse(edge.source, Set.empty).map(ids)
          val targetHeads = loops.getOrElse(edge.target, Set.empty).map(ids)
          //loops that are exited via edge
          val outHeads = sourceHeads -- targetHeads
          //loops that are entered via edge
          val inHeads = targetHeads -- sourceHeads
          if (outHeads.isEmpty && inHeads.isEmpty) map
          else {
            //at least one loop is entered or exited
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
      val withInfo = withIds.transformForceCopy({
        case node: Infoed =>
          val (pos, info, err) = node.meta
          info.getUniqueInfo[IdInfo] match {
            case Some(idInfo) =>
              //keep unique ids, if requested by caller
              val removed = (if(generateUniqueIds) { info } else {info.removeUniqueInfo[IdInfo] })
              val loopInfo = infos.getOrElse(idInfo.id, NoInfo)
              val updated = MakeInfoPair(removed, loopInfo)
              node.withMeta(pos, updated, err)
            case None => node
          }
        case node => node
      }, Traverse.TopDown)

      // return updated method
      (withInfo,  loopToWrittenVars)
  }

  private def naturalLoops[C <: Cfg[S, E], S, E](cfg: C, loops: Map[Block[S, E], Set[Block[S, E]]]) : (Map[Block[S, E], Set[Block[S, E]]], Dominators[S,E]) = {
    // check whether the control flow graph is reducible
    val dominators = new Dominators(cfg)
    if (!isReducible(cfg, dominators))
      throw new IllegalArgumentException("Control flow graph is not reducible.")

    // populate map that maps each block to the set of loop heads corresponding to all loops that contain the block
    val resultMap =
      cfg.edges
      .filter(dominators.isBackedge)
      .foldLeft[Map[Block[S, E], Set[Block[S, E]]]](loops) {
      case (current, edge) =>
        val head = edge.target
        collectBlocks(cfg, edge).foldLeft(current) {
          case (c, block) =>
            val existing = c.getOrElse(block, Set.empty)
            c.updated(block, existing + head)
        }
    }
    (resultMap, dominators)
  }

  private def writtenVariables(cfg: SilverCfg, dominators: Dominators[Stmt,Exp]) : Map[Block[Stmt,Exp], Seq[LocalVar]] = {
    cfg.edges
      .filter(dominators.isBackedge)
      .foldLeft[Map[Block[Stmt,Exp], Seq[LocalVar]]](Map.empty) {
        case (current, edge) =>
          val head = edge.target
          collectBlocks(cfg, edge).foldLeft(current) {
            case (c, block) =>
              val written = block.elements.flatMap {
                case Left(stmt) => stmt.writtenVars
                case Right(_) => Nil
              }
              val existing = c.getOrElse(head, Nil)
              c.updated(head, existing ++ written)
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
