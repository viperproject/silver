// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning.analysis

import org.jgrapht.Graph
import org.jgrapht.graph.DefaultEdge
import viper.silver.ast.{Declaration, LocalVarDecl, Program, Stmt}
import viper.silver.verifier.AbstractError

import scala.jdk.CollectionConverters.CollectionHasAsScala

trait SetGraphComparison extends VarAnalysisSet {
  private def computeSet(v: Declaration, blk: Stmt): Set[LocalVarDecl] = {
    get_tainted_vars_stmt(Set(v), blk).map(v => v.asInstanceOf[LocalVarDecl])
  }

  private def computeGraph(graph_analysis: VarAnalysisGraph, vars: Set[LocalVarDecl], blk: Stmt): (Graph[LocalVarDecl, DefaultEdge]/*, Map[LocalVarDecl,LocalVarDecl]*/) = {

    var allVertices: Map[LocalVarDecl, LocalVarDecl] = Map.empty

    /** add heap variables to vertices */
    allVertices += (graph_analysis.heap_vertex -> graph_analysis.createInitialVertex(graph_analysis.heap_vertex))

    vars.foreach(v => {
      val v_decl = v
      val v_init = graph_analysis.createInitialVertex(v_decl)
      allVertices += (v_decl -> v_init)

    })
    graph_analysis.compute_graph(blk, allVertices)
  }

  def compareGraphSet(prog: Program, reportError: AbstractError => Unit): Unit = {

    /**
      * SETS
      */
    val beginTimeSets = System.currentTimeMillis()
    var setForMethods: Map[String, Map[LocalVarDecl, Set[LocalVarDecl]]] = Map()
    prog.methods.foreach(m => {
      var vToSet: Map[LocalVarDecl, Set[LocalVarDecl]] = Map()
      val allParameters: Set[LocalVarDecl] = m.formalArgs.toSet.concat(m.formalReturns.toSet)
      m.formalArgs.foreach(arg => {
        vToSet += (arg -> computeSet(arg,m.bodyOrAssumeFalse).intersect(allParameters))
      })
      setForMethods += (m.name -> vToSet)

    })

    val endTimeSets = System.currentTimeMillis()
    val totalTimeSets = endTimeSets - beginTimeSets
    println("Time for Set analysis: " + totalTimeSets + "ms")
      /*
    val beginTimeSets = System.currentTimeMillis()
    var vToSet: Map[LocalVarDecl,Set[LocalVarDecl]] = Map()
    vars.foreach(v => {
      vToSet += (v.asInstanceOf[LocalVarDecl] -> (computeSet(v,blk).intersect(vars.map(d => d.asInstanceOf[LocalVarDecl]))))
    })
    val endTimeSets = System.currentTimeMillis()
    val totalTimeSets = endTimeSets - beginTimeSets


    println("Time for Set analysis: " + totalTimeSets + "ms")

       */


    /**
      * GRAPHS
      */

    val beginTimeGraphs = System.currentTimeMillis()
    val graph_analysis : VarAnalysisGraph = VarAnalysisGraph(prog, reportError)
    var graphForMethods: Map[String, Graph[LocalVarDecl,DefaultEdge]] = Map[String, Graph[LocalVarDecl,DefaultEdge]]()
    prog.methods.foreach(m => {
      graphForMethods += (m.name -> computeGraph(graph_analysis, m.formalArgs.toSet.concat(m.formalReturns.toSet), m.bodyOrAssumeFalse))
    })

    val endTimeGraphs = System.currentTimeMillis()
    val totalTimeGraphs = endTimeGraphs - beginTimeGraphs
    println("Time for Graph analysis: " + totalTimeGraphs + "ms")
    println("--------------------------------------------------------------------------")
      /*
    val beginTimeGraphs = System.currentTimeMillis()
    val graph_analysis: VarAnalysisGraph = VarAnalysisGraph(prog, reportError)
    val (graph: Graph[LocalVarDecl,DefaultEdge],_) = computeGraph(graph_analysis, vars,blk,prog, reportError)
    val endTimeGraphs = System.currentTimeMillis()
    val totalTimeGraphs = endTimeGraphs - beginTimeGraphs

    println("Time for Graph analysis: " + totalTimeGraphs + "ms")
    println("--------------------------------------------------------------------------")

       */


    /** compare for each variable */
    graphForMethods.foreach(mg => {
      val methodname = mg._1
      val graph = mg._2

      val set = setForMethods(methodname)

      prog.findMethod(methodname).formalArgs.foreach(arg => {
        val out_edges = graph.outgoingEdgesOf(graph_analysis.createInitialVertex(arg)).asScala.toSet

        var graph_vars: Set[LocalVarDecl] = Set()
        out_edges.foreach(e => {
          graph_vars += graph.getEdgeTarget(e)
        })

        val set_vars: Set[LocalVarDecl] = set(arg)

        if ((graph_vars - arg).equals(set_vars - arg)) {
          //println("SET AND GRAPH OF " + arg + " EQUAL")
        } else {
          println("SET AND GRAPH OF " + arg + " NOT EQUAL")
          println("set: " + set_vars)
          println("graph: " + graph_vars)
          println(graph_analysis.createDOT(graph))
          println("method:\n" + methodname)
        }
      })
    })
    /*
    vars.foreach(v => {
      val out_edges = graph.outgoingEdgesOf(graph_analysis.createInitialVertex(v.asInstanceOf[LocalVarDecl])).asScala.toSet

      var graph_vars: Set[LocalVarDecl] = Set()
      out_edges.foreach(e => {
        graph_vars += graph.getEdgeTarget(e)
      })

      val set_vars: Set[LocalVarDecl] = vToSet(v.asInstanceOf[LocalVarDecl])

      if ((graph_vars - v.asInstanceOf[LocalVarDecl]).equals(set_vars - v.asInstanceOf[LocalVarDecl])) {
        println("SET AND GRAPH OF " + v + " EQUAL")
      } else {
        println("SET AND GRAPH OF " + v + " NOT EQUAL")
        println("set: " + set_vars)
        println("graph: " + graph_vars)
        println(graph_analysis.createDOT(graph))
        println("method:\n" + m)
      }

    })
    */
  }
}
