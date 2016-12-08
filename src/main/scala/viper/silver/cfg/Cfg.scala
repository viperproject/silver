/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.cfg

/**
  * A control flow graph.
  *
  * The control flow graph is immutable. To overcome the inherent difficulties
  * of initializing immutable cyclic data structures the basic blocks do not
  * store the list of their predecessors and successors directly. First the
  * basic blocks are created. After that the edges that connect two basic blocks
  * each are created. The final control flow graph then offers methods to query
  * the predecessors, successors, etc. of the basic blocks.
  *
  * The control flow graph is parametric with respect to the statements and
  * expressions so that it can be reused more easily.
  *
  * @param blocks The list of blocks of the control flow graph.
  * @param edges  The list of edges of the control flow graph.
  * @param entry  The unique entry block of the control flow graph.
  * @param exit   The unique exit edge of the control flow graph.
  * @tparam S The type of the statements.
  * @tparam E The type of the expressions.
  */
class Cfg[S, E](val blocks: Seq[Block[S, E]], val edges: Seq[Edge[S, E]], val entry: Block[S, E], val exit: Block[S, E]) {
  /**
    * The map mapping blocks to the set of its ingoing edges.
    */
  private val inEdgesMap: Map[Int, Seq[Edge[S, E]]] =
    edges.groupBy(_.target.id)

  /**
    * The map mapping blocks to the set of its outgoing edges.
    */
  private val outEdgesMap: Map[Int, Seq[Edge[S, E]]] =
    edges.groupBy(_.source.id)

  /**
    * Returns the list of ingoing edges of the given block.
    *
    * @param block The block.
    * @return The list of ingoing edges.
    */
  def inEdges(block: Block[S, E]): Seq[Edge[S, E]] =
    inEdgesMap.getOrElse(block.id, Seq.empty)

  /**
    * Returns the list of outgoing edges of the given block.
    *
    * @param block The block.
    * @return The list of outgoing edges.
    */
  def outEdges(block: Block[S, E]): Seq[Edge[S, E]] =
    outEdgesMap.getOrElse(block.id, Seq.empty)

  /**
    * Returns the list of predecessors of the given block.
    *
    * @param block The block.
    * @return The list of predecessors.
    */
  def predecessors(block: Block[S, E]): Seq[Block[S, E]] =
    inEdges(block).map(_.source)

  /**
    * Returns the list of successors of the given block.
    *
    * @param block The block.
    * @return Te list of successors.
    */
  def successors(block: Block[S, E]): Seq[Block[S, E]] =
    outEdges(block).map(_.target)

  /**
    * Maps the given functions across the statements and expressions,
    * respectively, of the control flow graph.
    *
    * @param stmtMap The statement mapping function.
    * @param expMap  The expression mapping function.
    * @tparam S2 The return type of the statement mapping function.
    * @tparam E2 The return type of the expression mapping function.
    * @return The resulting control flow graph.
    */
  def map[S2, E2](stmtMap: S => S2, expMap: E => E2): Cfg[S2, E2] = {
    // map all blocks and create map mapping from old to new blocks
    val blockMap = this.blocks.map { block =>
      val mapped: Block[S2, E2] = block match {
        case StatementBlock(stmts) => StatementBlock(stmts.map(stmtMap))
        case PreconditionBlock(pres) => PreconditionBlock(pres.map(expMap))
        case PostconditionBlock(posts) => PostconditionBlock(posts.map(expMap))
        case LoopHeadBlock(invs, stmts) => LoopHeadBlock(invs.map(expMap), stmts.map(stmtMap))
        case ConstrainingBlock(vars, body) => ConstrainingBlock(vars.map(expMap), body.map(stmtMap, expMap))
      }
      block -> mapped
    }.toMap
    // extract list of mapped blocks
    val blocks: Seq[Block[S2, E2]] = blockMap.values.toList
    // map all edges
    val edges = this.edges.map { edge =>
      val mappedSource = blockMap.get(edge.source).get
      val mappedTarget = blockMap.get(edge.target).get
      edge match {
        case UnconditionalEdge(_, _, kind) => UnconditionalEdge(mappedSource, mappedTarget, kind)
        case ConditionalEdge(cond, _, _, kind) => ConditionalEdge(expMap(cond), mappedSource, mappedTarget, kind)
      }
    }
    // get mapped entry and exit block
    val entry = blockMap.get(this.entry).get
    val exit = blockMap.get(this.exit).get

    Cfg(blocks, edges, entry, exit)
  }

  /**
    * Returns a DOT representation of the control flow graph that can be
    * visualized using tools such as Graphviz.
    *
    * @return A DOT representation of the CFG.
    */
  def toDot(): String = {
    // escapes special characters
    def escape(str: String): String = str
      .replace("<", "\\<")
      .replace(">", "\\>")
      .replace("|", "\\|")

    // returns the name used for a basic block
    def id(block: Block[S, E]): String = s"BB${block.id}"

    def label(block: Block[S, E]): String = block match {
      case StatementBlock(stmts) =>
        s"${id(block)}|" + stmts.map(_.toString).map(escape).mkString("|")
      case _: PreconditionBlock[_, _] => s"${id(block)} (Precondition)"
      case _: PostconditionBlock[_, _] => s"${id(block)} (Postcondition)"
      case LoopHeadBlock(invs, stmts) =>
        s"${id(block)} (Loop Head)|" + invs.map(inv => "invariant " + escape(inv.toString)).mkString("|") + stmts.map(_.toString).map(escape).mkString("|")
      case _: ConstrainingBlock[_, _] => s"${id(block)} (Constraining)"
    }

    val blockStr = new StringBuilder()
    val edgeStr = new StringBuilder()

    // helper function that recursively processes all blocks
    def processBlocks(blocks: Seq[Block[S, E]]): Unit = {
      for (block <- blocks) {
        blockStr.append("  " + id(block) + " [\n")
        blockStr.append("    shape=\"record\"\n")
        blockStr.append("    label=\"" + label(block) + "\"\n")
        blockStr.append("  ];\n")
        block match {
          case c: ConstrainingBlock[S, E] =>
            processBlocks(c.body.blocks)
            processEdges(c.body.edges)
            edgeStr.append("  " + id(c) + " -> " + id(c.body.entry) + "[style=dotted];\n")
            edgeStr.append("  " + id(c.body.exit) + " -> " + id(c) + "[style=dotted];\n")
          case _ =>
        }
      }
    }

    // helper function that processes edges
    def processEdges(edges: Seq[Edge[S, E]]): Unit = {
      for (edge <- edges) {
        val suffix: Option[String] = edge.kind match {
          case Kind.In => Some("(in)")
          case Kind.Out => Some("(out)")
          case Kind.Unknown => Some("(??)")
          case _ => None
        }
        val label = edge match {
          case UnconditionalEdge(_, _, _) => suffix
          case ConditionalEdge(cond, _, _, _) =>
            if (suffix.isDefined) Some(escape(cond.toString) + " " + suffix.get)
            else Some(escape(cond.toString))
        }
        edgeStr.append("  " + id(edge.source) + " -> " + id(edge.target) + label.map(l => " [label=\"" + l + "\"]").getOrElse("") + ";\n")
      }
    }

    processBlocks(blocks)
    processEdges(edges)

    val dot = new StringBuilder()

    dot.append("digraph {\n")
    dot.append("  graph[rankdir=LR]")
    dot.append(blockStr)
    dot.append(edgeStr)
    dot.append("}\n")

    dot.toString
  }
}

object Cfg {
  def apply[S, E](blocks: Seq[Block[S, E]], edges: Seq[Edge[S, E]], entry: Block[S, E], exit: Block[S, E]): Cfg[S, E] = {
    new Cfg(blocks, edges, entry, exit)
  }

  def unapply[S, E](cfg: Cfg[S, E]): Option[(Seq[Block[S, E]], Seq[Edge[S, E]], Block[S, E], Block[S, E])] =
    Some((cfg.blocks, cfg.edges, cfg.entry, cfg.exit))
}

