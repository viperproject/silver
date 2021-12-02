// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import org.jgrapht.alg.connectivity.KosarajuStrongConnectivityInspector
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}

import scala.jdk.CollectionConverters._

protected object CallGraph {

  /**
   * @return sets, each containing recursively dependent vertices.
   */
  def mutuallyRecursiveVertices[V](graph: DefaultDirectedGraph[V, DefaultEdge]): Seq[Set[V]] = {
    val stronglyConnected = new KosarajuStrongConnectivityInspector(graph)
    val c = stronglyConnected.stronglyConnectedSets()
    c.asScala.map(_.asScala.toSet).toSeq
  }


  /**
   * @return vertices which are clearly non recursive and do not depend on other recursive vertices.
   */
  def clearlyNonRecursiveVertices[V](graph: DefaultDirectedGraph[V, DefaultEdge]): Set[V] = {

    @scala.annotation.tailrec
    def clearlyNonRecursiveVertices[V](graph: DefaultDirectedGraph[V, DefaultEdge], borderVertices: Seq[V], accumulator: Set[V]): Set[V] = {
      borderVertices.headOption match {
        case None => accumulator
        case Some(headVertex) =>
          // border vertices without head vertex and new border vertices added to it
          val newBorderVertices =
            graph.incomingEdgesOf(headVertex).asScala.foldLeft[Seq[V]](borderVertices.tail) {
              (b, e) =>
                val from = graph.getEdgeSource(e)
                graph.removeEdge(e)
                if (graph.outDegreeOf(from) == 0) {
                  // from vertex can be added to border vertices
                  b :+ from
                } else {
                  b
                }
            }
          clearlyNonRecursiveVertices(graph, newBorderVertices, accumulator + headVertex)
      }
    }

    // get all vertices which do not have any out-edge.
    val leaves = graph.vertexSet().asScala.toSeq.filter(key => graph.outDegreeOf(key) == 0)

    clearlyNonRecursiveVertices(graph, leaves, Set())
  }


}