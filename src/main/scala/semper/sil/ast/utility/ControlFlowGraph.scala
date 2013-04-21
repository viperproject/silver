package semper.sil.ast.utility

import semper.sil.ast._
import semper.sil.ast.NormalBlock
import semper.sil.ast.TerminalBlock
import semper.sil.ast.ConditionalBlock
import semper.sil.ast.FreshReadPermBlock
import semper.sil.ast.LoopBlock

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
        case LoopBlock(body, _, _, _, _) => Seq(body)
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
        case LoopBlock(_, cond, _, _, _) => s"while ($cond)"
        case FreshReadPermBlock(vars, _, _) => s"freshReadPerms ($vars)"
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
        if (b.isInstanceOf[LoopBlock]) nodes.append("shape=polygon sides=8 ")
        nodes.append("label=\""
          + label(b)
          + "\",];\n")

        // output edge and follow edges
        b match {
          case LoopBlock(body, _, _, _, succ) =>
            edges.append(s"    ${name(b)} -> ${name(body)} " + "[label=\"body\"];\n")
            edges.append(s"    ${name(b)} -> ${name(succ)} " + "[label=\"endLoop\"];\n")
          case FreshReadPermBlock(_, body, succ) =>
            edges.append(s"    ${name(b)} -> ${name(body)} " + "[label=\"body\"];\n")
            edges.append(s"    ${name(b)} -> ${name(succ)} " + "[label=\"succ\"];\n")
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
    res.append("digraph {\n")
    res.append("    node [shape=rectangle];\n\n")

    res.append(nodes)
    res.append(edges)

    // footer
    res.append("}\n")

    res.toString()
  }
}
