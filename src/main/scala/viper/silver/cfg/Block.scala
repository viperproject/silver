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
  private var id = new AtomicInteger(0)

  def nextId(): Int = {
    id.incrementAndGet()
  }
}

/**
  * A basic block containing statements.
  *
  * @param id    The id of the basic block.
  * @param stmts The list of statements of the basic block.
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
final class StatementBlock[S, E] private(val id: Int, val stmts: Seq[S])
  extends Block[S, E] {

  override lazy val elements: Seq[Either[S, E]] = stmts.map(Left(_))

  override def toString: String = s"StatementBlock($id)"
}

object StatementBlock {
  def apply[S, E](stmts: Seq[S] = Nil): StatementBlock[S, E] =
    new StatementBlock(Block.nextId(), stmts)

  def unapply[S, E](block: StatementBlock[S, E]): Option[Seq[S]] =
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
final class LoopHeadBlock[S, E] private(val id: Int, val invs: Seq[E], val stmts: Seq[S])
  extends Block[S, E] {
  override lazy val elements: Seq[Either[S, E]] = invs.map(Right(_)) ++ stmts.map(Left(_))

  override def toString: String = s"LoopHeadBlock($id)"
}

object LoopHeadBlock {
  def apply[S, E](invs: Seq[E] = Nil, stmts: Seq[S] = Nil): LoopHeadBlock[S, E] =
    new LoopHeadBlock(Block.nextId(), invs, stmts)

  def unapply[S, E](block: LoopHeadBlock[S, E]): Option[(Seq[E], Seq[S])] =
    Some((block.invs, block.stmts))
}

/**
  * A basic block corresponding to a constraining statement, that is, the
  * variables can be constrained inside the body.
  *
  * @param id   The id of the basic block.
  * @param vars The variables to constrain.
  * @param body The cfg corresponding to the body of the constraining statement.
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
final class ConstrainingBlock[S, E] private(val id: Int, val vars: Seq[E], val body: Cfg[S, E])
  extends Block[S, E] {
  override lazy val elements: Seq[Either[S, E]] = vars.map(Right(_))

  override def toString: String = s"ConstrainingBlock($id)"
}

object ConstrainingBlock {
  def apply[S, E](vars: Seq[E], body: Cfg[S, E]): ConstrainingBlock[S, E] =
    new ConstrainingBlock(Block.nextId(), vars, body)

  def unapply[S, E](block: ConstrainingBlock[S, E]): Option[(Seq[E], Cfg[S, E])] =
    Some((block.vars, block.body))
}