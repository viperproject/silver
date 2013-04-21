package semper.sil.ast.utility

import org.jgrapht._
import semper.sil.ast._
import org.jgrapht.graph._
import org.jgrapht.alg.StrongConnectivityInspector
import org.jgrapht.traverse.TopologicalOrderIterator

/**
 * Utility methods for functions.
 *
 * @author Stefan Heule
 */
object Functions {

  case class Edge[T](source: T, target: T)
  case class Factory[T]() extends EdgeFactory[T, Edge[T]] {
    def createEdge(source: T, target: T) =
      Edge(source, target)
  }

  /**
   * Returns the call graph of a given program (also considering specifications as calls).
   */
  def callgraph(p: Program): DirectedGraph[Function, Edge[Function]] = {
    val g = new DefaultDirectedGraph[Function, Edge[Function]](Factory[Function]())
    for (f <- p.functions) {
      g.addVertex(f)
    }
    def process(f: Function, e: Exp) {
      e visit {
        case FuncApp(f2, args) =>
          g.addEdge(f, f2)
      }
    }
    for (f <- p.functions) {
      process(f, f.exp)
      f.pres map (process(f, _))
      f.posts map (process(f, _))
    }
    g
  }

  /**
   * Computes the height of every function.  If the height h1 of a function f1 is
   * smaller than the height h2 of function f2, then f1 appears earlier in the
   * topological sort of the SCC of the callgraph.
   */
  def heights(p: Program): Map[Function, Int] = {
    // TODO: write a better implementation of the following code
    val result = collection.mutable.Map[Function, Int]()
    val g = callgraph(p)
    val scci = new StrongConnectivityInspector[Function, Edge[Function]](g)
    val scc = scci.stronglyConnectedSets()
    val sccg = new DefaultDirectedGraph[java.util.Set[Function], Edge[java.util.Set[Function]]](Factory[java.util.Set[Function]]())
    val sccit = scc.iterator()
    while (sccit.hasNext) {
      sccg.addVertex(sccit.next())
    }
    def find(f: Function): java.util.Set[Function] = {
      val it = scc.iterator()
      while (it.hasNext) {
        val n = it.next()
        if (n.contains(f)) return n
      }
      null
    }
    val edges = g.edgeSet().iterator()
    while (edges.hasNext) {
      val e = edges.next()
      sccg.addEdge(find(e.source), find(e.target))
    }
    val topo = new TopologicalOrderIterator[java.util.Set[Function], Edge[java.util.Set[Function]]](sccg)
    var h = 0
    while (topo.hasNext) {
      val cur = topo.next().iterator()
      while (cur.hasNext) {
        result(cur.next()) = h
      }
      h += 1
    }
    // add remainig vertices
    for (f <- p.functions) {
      if (!result.isDefinedAt(f)) {
        val tmp = find(f).iterator()
        while (tmp.hasNext) {
          result(tmp.next()) = h
        }
        h += 1
      }
    }
    result.toMap
  }
}
