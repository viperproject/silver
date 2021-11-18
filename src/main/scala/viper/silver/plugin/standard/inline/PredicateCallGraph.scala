package viper.silver.plugin.standard.inline

import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import viper.silver.ast.{Node, Predicate, PredicateAccess, PredicateAccessPredicate, Program}
import viper.silver.plugin.standard.termination.transformation.CallGraph

object PredicateCallGraph {

  type PredicateCallGraph = DefaultDirectedGraph[String, DefaultEdge]

  def graph(preds: Set[String], program: Program): PredicateCallGraph = {
    val graph = new PredicateCallGraph(classOf[DefaultEdge])
    preds.foreach(graph.addVertex)

    def process(src: String, node: Node): Unit =
      node.visit {
        case PredicateAccessPredicate(PredicateAccess(_, dst), _) =>
          if (preds(dst)) {
            graph.addEdge(src, dst)
          }
      }

    preds.foreach { pred =>
      program.findPredicate(pred).body.foreach(process(pred, _))
    }
    graph
  }

  def mutuallyRecursivePreds(graph: PredicateCallGraph): Set[String] =
    CallGraph.mutuallyRecursiveVertices(graph).filter(_.size > 1).flatten.toSet
}
