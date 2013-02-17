package semper.sil.ast.utility

import semper.sil.parser.Parser
import semper.sil.ast._

/** Utility methods for statements. */
object Statements {
  /** An empty statement. */
  val EmptyStmt = Seqn(Nil)()

  /**
   * Returns a list of all actual statements contained in a given statement.  That
   * is, all statements except `Seqn`, including statements in the body of loops, etc.
   */
  def children(s: Stmt): Seq[Stmt] = {
    s match {
      case While(_, _, body) => Seq(s) ++ children(body)
      case If(_, thn, els) => Seq(s) ++ children(thn) ++ children(els)
      case Seqn(ss) => ss
      case _ => List(s)
    }
  }
}

/** An utility object for consistency checking. */
object Consistency {

  /** Names that are not allowed for use in programs. */
  def reservedNames: Seq[String] = Parser.reserved

  /** Returns true iff the string `name` is a valid identifier. */
  def validIdentifier(name: String) = ("^" + Parser.identifier + "$").r.findFirstIn(name).isDefined

  /** Returns true iff the string `name` is a valid identifier, and not a reserved word. */
  def validUserDefinedIdentifier(name: String) = validIdentifier(name) && !reservedNames.contains(name)

  /** Returns true iff the two arguments are of equal length. */
  def sameLength[S, T](a: Seq[T], b: Seq[S]) = a.size == b.size

  /** Returns true iff the first argument can be assigned to the second one,
    * i.e. if the type of the first one is a subtype of the type of the second one. */
  def isAssignable(a: Typed, b: Typed) = a isSubtype b

  /** Returns true iff the arguments are equal of length and
    * the elements of the first argument are assignable to the corresponding elements of the second argument */
  def areAssignable(a: Seq[Typed], b: Seq[Typed]) = sameLength(a, b) && ((a zip b) forall (t => isAssignable(t._1, t._2)))

  /** Returns true iff there are no duplicates. */
  def noDuplicates[T](a: Seq[T]) = a.distinct.size == a.size

  /**
   * Is the control flow graph starting at `start` well-formed.  That is, does it have the following
   * properties:
   * <ul>
   * <li>It is acyclic.
   * <li>It has exactly one final block that all paths end in and that has no successors.
   * <li>Jumps are only within a loop, or out of (one or several) loops.
   * </ul>
   */
  // TODO: The last property about jumps is not checked as stated, but a stronger property (essentially forbidding many interesting jumps is checked)
  def isWellformedCfg(start: Block): Boolean = {
    val (ok, acyclic, terminalBlocks) = isWellformedCfgImpl(start)
    ok && acyclic && terminalBlocks.size == 1
  }

  /**
   * Implementation of well-formedness check. Returns (ok, acyclic, terminalBlocks) where `ok` refers
   * to the full graph and `acyclic` and `terminalBlocks` only to the outer-most graph (not any loops with nested
   * graphs).
   */
  private def isWellformedCfgImpl(start: Block, seenSoFar: Set[Block] = Set(), okSoFar: Boolean = true): (Boolean, Boolean, Set[TerminalBlock]) = {
    var ok = okSoFar
    start match {
      case t: TerminalBlock => (okSoFar, true, Set(t))
      case _ =>
        start match {
          case LoopBlock(body, cond, invs, succ) =>
            val (loopok, acyclic, terminalBlocks) = isWellformedCfgImpl(body)
            ok = okSoFar && loopok && acyclic && terminalBlocks.size == 1
          case _ =>
        }
        val seen = seenSoFar union Set(start)
        var terminals = Set[TerminalBlock]()
        var acyclic = true
        for (b <- start.succs) {
          if (seen contains b.dest) {
            acyclic = false
          }
          val (okrec, a, t) = isWellformedCfgImpl(b.dest, seen, ok)
          ok = ok && okrec
          acyclic = acyclic && a
          terminals = terminals union t
        }
        (ok, acyclic, terminals)
    }
  }
}

/** A utility object for control flow graphs. */
object ControlFlowGraph {

  /**
   * Performs a breadth-first search over a control flow graph.
   */
  def bfs(block: Block)(f: Block => Unit) {
    val worklist = collection.mutable.Queue[Block]()
    worklist.enqueue(block)
    val visited = collection.mutable.Set[Block]()

    while (!worklist.isEmpty) {
      val b = worklist.dequeue()
      val succsAndBody = (b.succs map (_.dest)) ++ (b match {
        case LoopBlock(body, _, _, _) => Seq(body)
        case _ => Nil
      })
      worklist.enqueue((succsAndBody filterNot (visited contains _)): _*)
      visited ++= succsAndBody
      f(b)
    }
  }

  /**
   * Returns a DOT representation of the control flow graph that can be visualized using
   * tools such as Graphviz.
   */
  def toDot(block: Block): String = {
    val nodes = new StringBuilder()
    val edges = new StringBuilder()

    def name(b: Block) = b.hashCode.toString
    def label(b: Block) = {
      val r = b match {
        case LoopBlock(_, cond, _, _) => s"while ($cond)"
        case TerminalBlock(stmt) => stmt.toString
        case NormalBlock(stmt, _) => stmt.toString
        case ConditionalBlock(stmt, cond, _, _) =>
          if (stmt.toString == "") s"if ($cond)"
          else s"$stmt\n\nif ($cond)"
      }
      r.replaceAll("\\n", "\\\\l")
    }

    bfs(block) {
      b =>
      // output node
        nodes.append("    " + name(b) + " [")
        if (b.isInstanceOf[LoopBlock]) nodes.append("shape=polygon sides=8 ");
        nodes.append("label=\""
          + label(b)
          + "\",];\n")

        // output edge and follow edges
        b match {
          case LoopBlock(body, _, _, succ) =>
            edges.append(s"    ${name(b)} -> ${name(body)} " + "[label=\"body\"];\n")
            edges.append(s"    ${name(b)} -> ${name(succ)} " + "[label=\"endLoop\"];\n")
          case TerminalBlock(stmt) =>
          case NormalBlock(_, succ) =>
            edges.append(s"    ${name(b)} -> ${name(succ)};\n")
          case ConditionalBlock(_, _, thn, els) =>
            edges.append(s"    ${name(b)} -> ${name(thn)} " + "[label=\"then\"];\n")
            edges.append(s"    ${name(b)} -> ${name(els)} " + "[label=\"else\"];\n")
        }
    }

    val res = new StringBuilder()

    // header
    res.append("digraph {\n");
    res.append("    node [shape=rectangle];\n\n");

    res.append(nodes)
    res.append(edges)

    // footer
    res.append("}\n");

    res.toString()
  }
}
