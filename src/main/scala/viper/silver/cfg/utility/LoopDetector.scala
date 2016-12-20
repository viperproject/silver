package viper.silver.cfg.utility

import viper.silver.cfg._

/**
  * An object that provides
  */
object LoopDetector {
  /**
    * Detects loops in a control flow graph and returns a version of the control
    * flow graph where the edges entering and leaving loops are marked.
    *
    * @param cfg The control flow graph.
    * @tparam S The type of the statements.
    * @tparam E The type of the expressions.
    * @return The control flow graph where the edges entering and leaving loops
    *         are marked.
    */
  def detect[C <: Cfg[S, E], S, E](cfg: C): C = detect[C, S, E](cfg, Map.empty[Int, Int], Map.empty[Int, Int])

  /**
    * Detects loops in a control flow graph and returns a version of the control
    * flow graph where the edges entering and leaving loops are marked.
    *
    * Additionally to the control flow graph some known information about the
    * loop can be passed.
    *
    * @param cfg    The control flow graph.
    * @param loops  The map mapping the ids of basic blocks of a (known) loop to
    *               the id of the basic block at the head of that loop.
    * @param parent The map mapping the ids of basic blocks at the head of a
    *               (known) loop to the id of the basic block that is at the
    *               head of the parent loop.
    * @tparam S The type of the statements.
    * @tparam E The type of the expressions.
    * @return The control flow graph where the edges entering and leaving loops
    *         are marked.
    */
  def detect[C <: Cfg[S, E], S, E](cfg: C, loops: Map[Int, Int], parent: Map[Int, Int]): C = {
    // TODO: Implement the actual loop detection algorithm.

    val edges = cfg.edges.map { case edge =>
      val sourceLoop = loops.get(edge.source.id)
      val targetLoop = loops.get(edge.target.id)

      val kind = (sourceLoop, targetLoop) match {
        case (None, Some(_)) => Kind.In
        case (Some(_), None) => Kind.Out
        case (Some(a), Some(b)) =>
          if (sourceLoop == parent.get(b)) Kind.In
          else if (targetLoop == parent.get(a)) {
            // TODO: Handle cases where we jump out of several loops
            Kind.Out
          } else {
            assert(a == b)
            Kind.Normal
          }
        case _ => Kind.Normal
      }

      edge match {
        case UnconditionalEdge(source, target, _) => UnconditionalEdge(source, target, kind)
        case ConditionalEdge(cond, source, target, _) => ConditionalEdge(cond, source, target, kind)
      }
    }

    cfg.copy(edges = edges, entry = cfg.entry, exit = cfg.exit).asInstanceOf[C]
  }
}
