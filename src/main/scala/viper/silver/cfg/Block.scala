// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.cfg

import java.util.concurrent.atomic.AtomicInteger

/**
  * A basic block of a control flow graph.
  *
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
sealed trait Block[S, E] {
  /**
    * Returns the id of the basic block.
    *
    * @return The id of the basic block.
    */
  def id: Int

  /**
    * Returns the list of elements stored in the basic block.
    *
    * @return The list of elements stored in the basic block.
    */
  def elements: Seq[Either[S, E]]
}

object Block {
  private val id = new AtomicInteger(0)

  def nextId(): Int = {
    id.incrementAndGet()
  }
}

/**
  * A basic block containing statements.
  *
  * @param id     The id of the basic block.
  * @param stmts  The list of statements of the basic block.
  * @param invs   The list of invariants of this basic block *in case* it turns out to be a loop head.
  * @param loopId The loopId of this basic block *in case* it turns out to be a loop head.
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
final class StatementBlock[S, E] private(val id: Int, val stmts: Seq[S], val invs: Option[Seq[E]] = None, val loopId: Option[Option[Int]] = None)
  extends Block[S, E] {

  override lazy val elements: Seq[Either[S, E]] = stmts.map(Left(_))

  override def toString: String = s"StatementBlock($id)"
}

object StatementBlock {
  def apply[S, E](stmts: Seq[S] = Nil): StatementBlock[S, E] =
    new StatementBlock(Block.nextId(), stmts)

  def apply[S, E](stmts: Seq[S], invs: Seq[E], loopId: Option[Int]): StatementBlock[S, E] =
    new StatementBlock(Block.nextId(), stmts, Some(invs), Some(loopId))

  def unapply[S, E](block: StatementBlock[S, E]): Some[Seq[S]] =
    Some(block.stmts)
}

/**
  * A basic block containing a precondition.
  *
  * @param id   The id of the basic block.
  * @param pres The list of preconditions of the basic block.
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
final class PreconditionBlock[S, E] private(val id: Int, val pres: Seq[E])
  extends Block[S, E] {
  override lazy val elements: Seq[Either[S, E]] = pres.map(Right(_))

  override def toString: String = s"PreconditionBlock($id)"
}

object PreconditionBlock {
  def apply[S, E](pres: Seq[E]): PreconditionBlock[S, E] =
    new PreconditionBlock(Block.nextId(), pres)

  def unapply[S, E](block: PreconditionBlock[S, E]): Option[Seq[E]] =
    Some(block.pres)
}

/**
  * A basic block containing a postcondition.
  *
  * @param id    The id of the basic block.
  * @param posts The list of postconditions of the basic block.
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
final class PostconditionBlock[S, E] private(val id: Int, val posts: Seq[E])
  extends Block[S, E] {
  override lazy val elements: Seq[Either[S, E]] = posts.map(Right(_))

  override def toString: String = s"PostconditionBlock($id)"
}

object PostconditionBlock {
  def apply[S, E](posts: Seq[E]): PostconditionBlock[S, E] =
    new PostconditionBlock(Block.nextId(), posts)

  def unapply[S, E](block: PostconditionBlock[S, E]): Option[Seq[E]] =
    Some(block.posts)
}

/**
  * A basic block containing representing a loop head with a list of invariants
  * and a list of statements.
  *
  * @param id    The id of the basic block.
  * @param invs  The list of invariants of the basic block.
  * @param stmts The list of statements of the basic block.
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
final class LoopHeadBlock[S, E] private(val id: Int, val invs: Seq[E], val stmts: Seq[S], val loopId: Option[Int])
  extends Block[S, E] {
  override lazy val elements: Seq[Either[S, E]] = invs.map(Right(_)) ++ stmts.map(Left(_))

  override def toString: String = {
    val ids = if (loopId.isDefined) s"$id, ${loopId.get}" else id.toString
    s"LoopHeadBlock($ids)"
  }
}

object LoopHeadBlock {
  def apply[S, E](invs: Seq[E] = Nil, stmts: Seq[S] = Nil, loopId: Option[Int] = None): LoopHeadBlock[S, E] =
    new LoopHeadBlock(Block.nextId(), invs, stmts, loopId)

  def unapply[S, E](block: LoopHeadBlock[S, E]): Some[(Seq[E], Seq[S], Option[Int])] =
    Some((block.invs, block.stmts, block.loopId))
}