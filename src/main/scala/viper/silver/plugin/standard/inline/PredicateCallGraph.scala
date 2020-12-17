package viper.silver.plugin.standard.inline

import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import viper.silver.ast.{Node, Predicate, PredicateAccess, PredicateAccessPredicate, Program}
import viper.silver.plugin.standard.termination.transformation.CallGraph

object PredicateCallGraph {

  type PredicateCallGraph = DefaultDirectedGraph[Predicate, DefaultEdge]

  def graph(preds: Set[Predicate], program: Program): PredicateCallGraph = {
    val graph = new DefaultDirectedGraph[Predicate, DefaultEdge](classOf[DefaultEdge])
    preds.foreach(graph.addVertex)

    def process(pred: Predicate, node: Node): Unit =
      node.visit {
        case PredicateAccessPredicate(PredicateAccess(_, name), _) =>
          graph.addEdge(pred, program.findPredicate(name))
      }

    preds.foreach { pred =>
      pred.body.foreach(process(pred, _))
    }
    graph
  }

  def mutuallyRecursivePreds(graph: PredicateCallGraph): Set[Predicate] =
    CallGraph.mutuallyRecursiveVertices(graph).filter(_.size > 1).flatten.toSet
}
