// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.cfg.silver

import viper.silver.ast.{Exp, LocalVar, Stmt}
import viper.silver.cfg._
import viper.silver.cfg.silver.SilverCfg.{SilverBlock, SilverEdge, SilverLoopHeadBlock}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * A silver control flow graph.
  */
class SilverCfg(val blocks: Seq[SilverBlock], val edges: Seq[SilverEdge], val entry: SilverBlock, val exit: Option[SilverBlock])
  extends Cfg[Stmt, Exp] {

  private val cache: mutable.Map[SilverLoopHeadBlock, Seq[LocalVar]] = mutable.Map()

  /**
    * Computes all local variables that are written to in the loop with the
    * given basic block as loop head.
    *
    * @param loop The basic block at the head of the loop.
    * @return The list of written variables.
    */
  def writtenVars(loop: SilverLoopHeadBlock): Seq[LocalVar] = {
    val cached = cache.get(loop)
    if (cached.isDefined) cached.get
    else {
      val visited: mutable.Set[SilverBlock] = mutable.Set()
      val queue: mutable.Queue[(SilverBlock, Int)] = mutable.Queue()
      val list: ListBuffer[LocalVar] = ListBuffer()

      queue.enqueue((loop, 0))
      visited.add(loop)

      while (queue.nonEmpty) {
        // get current block
        val (block, depth) = queue.dequeue()

        // extract written variables
        val written = block.elements.flatMap {
          case Left(stmt) => stmt.writtenVars
          case Right(_) => Seq.empty
        }
        list.append(written: _*)

        // process successors
        outEdges(block).foreach { edge =>
          // get depth of successor
          val successorDepth = edge.kind match {
            case Kind.In => depth + 1
            case Kind.Out => depth - 1
            case _ => depth
          }
          val successor = edge.target
          // add successors to the queue if we are still inside the loop (i.e.
          // the depth is non-negative) and the successor has not been visited.
          if (successorDepth >= 0 && !visited.contains(successor)) {
            queue.enqueue((successor, successorDepth))
            visited.add(successor)
          }
        }
      }

      // remember result
      val result = list.distinct.toList
      cache.put(loop, result)

      // return result
      result
    }
  }

  override def copy(blocks: Seq[SilverBlock] = blocks,
                    edges: Seq[SilverEdge] = edges,
                    entry: SilverBlock = entry,
                    exit: Option[SilverBlock] = exit): SilverCfg =
    SilverCfg(blocks, edges, entry, exit

  private def findJoinPoint(queueInit: Iterable[SilverBlock],
                            visitedInit: Iterable[SilverBlock],
                            // We never enqueue loopHeads which we already have seen.
                            // This would lead to non-termination.
                            loopHeadsSeen: Iterable[SilverBlock],
                            getNext: SilverBlock => Iterable[SilverBlock])
  : (Option[SilverBlock], mutable.Map[SilverBlock, SilverBlock]) = {

    var queue = mutable.Queue.from(queueInit)
    var visited: Vector[SilverBlock] = Vector.from(visitedInit)
    val map = mutable.Map[SilverBlock, SilverBlock]()
    var loopHeads: Vector[SilverBlock] = Vector.from(loopHeadsSeen)

    while (queue.nonEmpty) {
      val curr = queue.dequeue()
      val visitNext = curr match {
        case curr =>
          if (!visited.contains(curr)) {
            visited :+= curr
            if (curr.isInstanceOf[SilverLoopHeadBlock]) {
              loopHeads :+= curr
            }
            getNext(curr) match {
              case out @ Seq() => out
              case out @ Seq(_) => out
              case out @ Seq(_, _) =>
                val (joinPoint, innerMap) =
                  findJoinPoint(out.filter(!loopHeads.contains(_)), Seq(curr), loopHeads, getNext)
                map ++= innerMap
                joinPoint match {
                  case Some(joinPoint) =>
                    map += curr -> joinPoint
                  case None => ()
                }
                joinPoint
              case _ => sys.error("At most two outgoing edges expected.")
            }
          } else {
            return (Some(curr), map)
          }
      }

      // Avoid re-visiting already seen loop heads.
      queue = queue.enqueueAll(visitNext.iterator.filter(!loopHeads.contains(_)))
    }
    (None, map)
  }

  /**
    * Computes all local variables that are written to in the loop with the
    * given basic block as loop head.
    *
    * @return Mapping from all branch points to join points.
    */
  lazy val joinPoints: mutable.Map[SilverBlock, SilverBlock] = {
    val (jp, map) = findJoinPoint(Seq(entry), Seq.empty, Seq.empty, successors)
    assert(jp.isEmpty)
    map
  }
}

object SilverCfg {
  type SilverBlock = Block[Stmt, Exp]
  type SilverLoopHeadBlock = LoopHeadBlock[Stmt, Exp]
  type SilverEdge = Edge[Stmt, Exp]

  def apply(blocks: Seq[SilverBlock], edges: Seq[SilverEdge], entry: SilverBlock, exit: Option[SilverBlock]) =
    new SilverCfg(blocks, edges, entry, exit)

  def unapply(cfg: SilverCfg): Option[(Seq[SilverBlock], Seq[SilverEdge], SilverBlock, Option[SilverBlock])] =
    Some((cfg.blocks, cfg.edges, cfg.entry, cfg.exit))
}