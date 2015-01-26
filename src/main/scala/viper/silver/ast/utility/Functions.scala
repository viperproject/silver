/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import scala.collection.JavaConversions._
import org.jgrapht.{DirectedGraph, EdgeFactory}
import org.jgrapht.alg.{CycleDetector, StrongConnectivityInspector}
import org.jgrapht.graph.DefaultDirectedGraph
import org.jgrapht.traverse.TopologicalOrderIterator
import viper.silver.ast._

/**
 * Utility methods for functions.
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
  def getCallgraph(p: Program): DirectedGraph[Function, Edge[Function]] = {
    val g = new DefaultDirectedGraph[Function, Edge[Function]](Factory[Function]())
    for (f <- p.functions) {
      g.addVertex(f)
    }
    def process(f: Function, e: Exp) {
      e visit {
        case FuncApp(f2name, args) =>
          g.addEdge(f, p.findFunction(f2name))
      }
    }
    for (f <- p.functions) {
      process(f, f.body)
      f.pres map (process(f, _))
      f.posts map (process(f, _))
    }
    g
  }

  /**
    * Computes the height of every function.  If the height h1 of a function f1 is
    * smaller than the height h2 of function f2, then f1 appears earlier in the
    * topological sort of the SCC of the callgraph.
    *
    * Phrased differently, if a function f1 (transitively) calls another function
    * f2, then f2 will have a greater height than f1 (or the same, if f2 in turn
    * calls f1).
    */
  def heights(program: Program): Map[Function, Int] = {
    val result = collection.mutable.Map[Function, Int]()

    /* Compute the call-graph over all functions in the given program.
     * An edge from f1 to f2 denotes that f1 calls f2, either in the function
     * body or in the specifications.
     */
    val callGraph = getCallgraph(program)

///* debugging */
//    val functionVNP = new org.jgrapht.ext.VertexNameProvider[Function] {
//      def getVertexName(vertex: Function) = vertex.name
//    }
//
//    val dotExporter = new org.jgrapht.ext.DOTExporter(functionVNP, //new org.jgrapht.ext.IntegerNameProvider[Function](),
//                                                      functionVNP,
//                                                      null)
//
//    dotExporter.export(new java.io.FileWriter("callgraph.dot"), callGraph.asInstanceOf[Graph[Function, Nothing]])
///* /debugging */

    /* Get all strongly connected components (SCCs) of the call-graph, represented as
     * sets of functions.
     */
    val stronglyConnectedSets = new StrongConnectivityInspector(callGraph).stronglyConnectedSets()

    /* Will represent the condensation of the call-graph, i.e., the call-graph,
     * but where each strongly connected component has been condensed into a
     * single node.
     */
    val condensedCallGraph = new DefaultDirectedGraph(Factory[java.util.Set[Function]]())

    /* Add each SCC as a vertex to the condensed call-graph */
    for (v <- stronglyConnectedSets) {
      condensedCallGraph.addVertex(v)
    }

    def condensationOf(func: Function): java.util.Set[Function] =
      stronglyConnectedSets.find(_ contains func).get

    /* Add edges from the call-graph (between individual functions) as edges
     * between their corresponding SCCs in the condensed call-graph, but only
     * if this does not result in a cycle.
     */
    for (e <- callGraph.edgeSet()) {
      val sourceSet = condensationOf(e.source)
      val targetSet = condensationOf(e.target)

      if (sourceSet != targetSet)
        condensedCallGraph.addEdge(sourceSet, targetSet)
    }

///* debugging */
//    val functionSetVNP = new org.jgrapht.ext.VertexNameProvider[java.util.Set[Function]] {
//      def getVertexName(vertex: java.util.Set[Function]) = vertex.map(_.name).mkString(", ")
//    }
//
//    val functionSetIDP = new org.jgrapht.ext.VertexNameProvider[java.util.Set[Function]] {
//      def getVertexName(vertex: java.util.Set[Function]) = s""""${vertex.map(_.name).mkString(", ")}""""
//    }
//
//    val dotExporter2 = new org.jgrapht.ext.DOTExporter(functionSetIDP, // new org.jgrapht.ext.IntegerNameProvider[java.util.Set[Function]](),
//                                                       functionSetVNP,
//                                                       null)
//    dotExporter2.export(new java.io.FileWriter("sccg.dot"), sccg.asInstanceOf[Graph[java.util.Set[Function], Nothing]])
///* /debugging */

    /* The behaviour of TopologicalOrderIterator is undefined if it is applied
     * to a cyclic graph, hence this check.
     */
    assert(!new CycleDetector(condensedCallGraph).detectCycles(),
           "Expected acyclic graph, but found at least one cycle")

    /* Traverse the condensed call-graph in topological order while increasing
     * the function height. Each function in a condensed vertex (an SCC) gets
     * the same height.
     */
    var height = 0
    for (condensation <- new TopologicalOrderIterator(condensedCallGraph)) {
      for (func <- condensation) {
        result(func) = height
      }

      height += 1
    }

    result.toMap
  }

  /**
   * Helper method for finding the recursive function calls in f's body, and pairing them with the unfolding expressions they occur under.
   * This can be useful for axiomatisation of functions, and possible for termination checking.
   *
   * Note that the LHS of unfolding expressions is not recursed into (we might want to revisit this decision).
   *
   * @param f The function whose body we want to analyse
   * @return A sequence of pairs of function application with the sequence of unfoldings (outermost-first) under which they occur
   */
  def recursiveCallsAndSurroundingUnfoldings(f : Function) : Seq[(FuncApp,Seq[Unfolding])] = {
    var result: Seq[(FuncApp, Seq[Unfolding])] = Seq()

    def recordCallsAndUnfoldings(e: Node, ufs: Seq[Unfolding]) {
      e.shallowCollect {
      case uf@Unfolding (acc, body) =>
        recordCallsAndUnfoldings (body, ufs :+ uf) // note: acc is not recursively-processed - we may want to revisit this decision
      case fa@FuncApp (func, args) =>
        result +:= (fa, ufs)
        args.map ((n) => recordCallsAndUnfoldings (n, ufs) )
      }
    }
      recordCallsAndUnfoldings (f.body, Seq())
      result
  }
}
