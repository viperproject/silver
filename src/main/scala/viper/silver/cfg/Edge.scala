// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.cfg

/**
  * The enumeration used to indicate the kind of an edge. An edge is either a
  * normal edge, an edge that enters a loop, or an edge that leaves a loop.
  */
object Kind extends Enumeration {
  val Normal = Value("normal")
  val In = Value("in")
  val Out = Value("out")
  val Unknown = Value("unknown")
}

/**
  * An edge of a control flow graph.
  *
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
sealed trait Edge[S, E] {
  /**
    * Returns the basic block at the source of the edge.
    *
    * @return The basic block at the source of the edge.
    */
  def source: Block[S, E]

  /**
    * Returns the basic block at the target of the edge.
    *
    * @return The basic block at the target of the edge.
    */
  def target: Block[S, E]

  /**
    * Returns the kind of the edge.
    *
    * @return The kind of the edge.
    */
  def kind: Kind.Value

  /**
    * Returns true if the edge is entering a loop.
    *
    * @return True if the edge is entering a loop.
    */
  def isIn: Boolean = kind == Kind.In

  /**
    * Returns true if the edge is leaving a loop.
    *
    * @return True if the edge is leaving a loop.
    */
  def isOut: Boolean = kind == Kind.Out
}

/**
  * An unconditional edge of a control flow graph.
  *
  * @param source The basic block at the source of the edge.
  * @param target The basic block at the target of the edge.
  * @param kind   The kind of the edge.
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
final case class UnconditionalEdge[S, E](source: Block[S, E], target: Block[S, E], kind: Kind.Value = Kind.Unknown)
  extends Edge[S, E]

/**
  * A conditional edge of a control flow graph.
  *
  * @param condition The condition associated with the edge.
  * @param source    The basic block at the source of the edge.
  * @param target    The basic block at the target of the edge.
  * @param kind      The kind of the edge.
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
final case class ConditionalEdge[S, E](condition: E, source: Block[S, E], target: Block[S, E], kind: Kind.Value = Kind.Unknown)
  extends Edge[S, E]