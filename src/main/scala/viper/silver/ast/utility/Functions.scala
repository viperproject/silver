// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast._
import org.jgrapht.alg.cycle.CycleDetector
import org.jgrapht.alg.connectivity.GabowStrongConnectivityInspector
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import org.jgrapht.traverse.TopologicalOrderIterator

import scala.collection.immutable.ListMap
import scala.collection.mutable.{ListBuffer, Set => MSet}
import scala.jdk.CollectionConverters._

/**
 * Utility methods for functions.
 */
object Functions {

  type FuncName = String

  case class Edge[T](source: T, target: T)

  def allSubexpressions(func: Function): Seq[Exp] = func.pres ++ func.posts ++ func.body
  def allSubexpressionsIncludingUnfoldings(program: Program)(func: Function): Seq[Exp] = {
    var visitedPredicates = Set[String]()
    var subexpressions = allSubexpressions(func)
    val unfoldings = new ListBuffer[Unfolding]
    unfoldings ++= (subexpressions map (e => e.deepCollect{case u@Unfolding(_, _) => u})).flatten
    var i = 0
    while (i < unfoldings.length){
      val current = unfoldings(i)
      val name = current.acc.loc.predicateName
      if (!visitedPredicates.contains(name)){
        visitedPredicates += name
        val pred = program.findPredicate(name)
        if (pred.body.isDefined) {
          val bodyExp : Exp = pred.body.get
          subexpressions ++= Seq(bodyExp)
          unfoldings ++= bodyExp.deepCollect { case u@Unfolding(_, _) => u }
        }
      }
      i += 1
    }
    subexpressions
  }

  /** Returns the call graph of a given program (also considering specifications as calls).
    *
    * TODO: Memoize invocations of `getFunctionCallgraph`. Note that it's unclear how to derive a useful key from `subs`
    */
  def getFunctionCallgraph(program: Program, subs: Function => Seq[Exp] = allSubexpressions)
                          : DefaultDirectedGraph[FuncName, DefaultEdge] = {
    val graph = new DefaultDirectedGraph[FuncName, DefaultEdge](classOf[DefaultEdge])

    for (f <- program.functions) {
      graph.addVertex(f.name)
    }

    def process(f: Function, e: Exp): Unit = {
      e visit {
        case FuncApp(f2name, _) =>
          graph.addEdge(f.name, f2name)
      }
    }

    for (f <- program.functions) {
      subs(f) foreach (process(f, _))
    }

    graph
  }
  /**
    * Computes the height of every function.  If the height h1 of a function f1 is
    * smaller than the height h2 of function f2, then f1 appears earlier in the
    * topological sort of the SCC of the callgraph.
    *
    * Phrased differently, if a function f1 (transitively) calls another function
    * f2, then f2 will have a greater height than f1 (or the same, if f2 in turn
    * calls f1). If the flag considerUnfoldings is set, calls to f2 in the body of
    * a predicate that is unfolded by f1 are also taken into account.
    */
  def heights(program: Program, considerUnfoldings: Boolean = false): Map[FuncName, Int] = {
    val result = collection.mutable.Map[FuncName, Int]()

    /* Compute the call-graph over all functions in the given program.
     * An edge from f1 to f2 denotes that f1 calls f2, either in the function
     * body or in the specifications. If the flag considerUnfoldings is set,
     * an edge can also mean that f1 unfolds a predicate in whose body f2
     * is called.
     */
    val callGraph = if (considerUnfoldings){
      getFunctionCallgraph(program, allSubexpressionsIncludingUnfoldings(program))
    }else{
      getFunctionCallgraph(program, allSubexpressions)
    }

    /* Get all strongly connected components (SCCs) of the call-graph, represented as
     * sets of functions.
     */
    val stronglyConnectedSets = new GabowStrongConnectivityInspector(callGraph).stronglyConnectedSets().asScala

    /* Will represent the condensation of the call-graph, i.e., the call-graph,
     * but where each strongly connected component has been condensed into a
     * single node.
     */
    val condensedCallGraph = new DefaultDirectedGraph[MSet[FuncName], DefaultEdge](classOf[DefaultEdge])

    /* Add each SCC as a vertex to the condensed call-graph */
    stronglyConnectedSets.foreach(v => condensedCallGraph.addVertex(v.asScala))

    def condensationOf(func: FuncName): MSet[FuncName] =
      stronglyConnectedSets.find(_ contains func).get.asScala

    /* Add edges from the call-graph (between individual functions) as edges
     * between their corresponding SCCs in the condensed call-graph, but only
     * if this does not result in a cycle.
     */
    for (e <- callGraph.edgeSet().asScala) {
      val sourceSet = condensationOf(callGraph.getEdgeSource(e))
      val targetSet = condensationOf(callGraph.getEdgeTarget(e))

      if (sourceSet != targetSet)
        condensedCallGraph.addEdge(sourceSet, targetSet)
    }

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
    for (condensation <- new TopologicalOrderIterator(condensedCallGraph).asScala) {
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

    def recordCallsAndUnfoldings(e: Node, ufs: Seq[Unfolding]): Unit = {
      e.shallowCollect {
      case Let(_, e, bod) => recordCallsAndUnfoldings(e.replace(e, bod), ufs)
      case uf@Unfolding (_, body) =>
        recordCallsAndUnfoldings (body, ufs :+ uf) // note: acc is not recursively-processed - we may want to revisit this decision
      case fa@FuncApp (_, args) =>
        result +:= (fa, ufs)
        args.foreach ((n) => recordCallsAndUnfoldings (n, ufs) )
      }
    }

    f.body foreach (recordCallsAndUnfoldings(_, Seq()))

    result
  }

  /** Returns all cycles formed by functions that (transitively) recurse via their precondition.
    *
    * @param program The program that defines the functions to check for cycles.
    * @return A map from functions to sets of functions. If a function `f` maps to a set of
    *         functions `fs`, then `f` (transitively) recurses via its precondition, and the
    *         formed cycles involves the set of functions `fs`.
    */
  def findFunctionCyclesViaPreconditions(program: Program): Map[Function, Set[FuncName]] = {
    findFunctionCyclesVia(program, func => func.pres, allSubexpressions)
  }

  /** Returns all cycles formed by functions that (transitively through certain subexpressions)
    * recurse via certain expressions.
    *
    * @param program The program that defines the functions to check for cycles.
    * @param via The expression the cycle has to go through.
    * @param subs The expressions the cycle can go through transitively
    * @return A map from functions to sets of functions. If a function `f` maps to a set of
    *         functions `fs`, then `f` (transitively) recurses via, and the
    *         formed cycles involves the set of functions `fs`.
    */
  def findFunctionCyclesVia(program: Program, via: Function => Seq[Exp], subs: Function => Seq[Exp] = allSubexpressions)
      :Map[Function, Set[FuncName]] = {
    def viaSubs(entryFunc: Function)(otherFunc: Function): Seq[Exp] =
      if (otherFunc == entryFunc)
        via(otherFunc)
      else
        subs(otherFunc)

    val res = program.functions.flatMap(func => {
      val graph = getFunctionCallgraph(program, viaSubs(func))
      findCycles(graph, func)
    })
    ListMap.from(res)
  }

  /** Returns all cycles formed by functions that (transitively through certain subexpressions)
    * recurse via certain expressions. This is an optimized version of `findFunctionCyclesVia` in case
    * `via` and `subs` are equivalent.
    *
    * @param program The program that defines the functions to check for cycles.
    * @param via     The expression the cycle has to go through.
    * @return A map from functions to sets of functions. If a function `f` maps to a set of
    *         functions `fs`, then `f` (transitively) recurses via, and the
    *         formed cycles involves the set of functions `fs`.
    */
  def findFunctionCyclesViaOptimized(program: Program, via: Function => Seq[Exp])
  : Map[Function, Set[FuncName]] = {
    val graph = getFunctionCallgraph(program, via)
    val res = program.functions.flatMap(func => {
      findCycles(graph, func)
    })
    ListMap.from(res)
  }

  private def findCycles(graph: DefaultDirectedGraph[FuncName, DefaultEdge], func: Function): Option[(Function, Set[FuncName])] = {
    val cycleDetector = new CycleDetector(graph)
    val cycle = cycleDetector.findCyclesContainingVertex(func.name).asScala
    if (cycle.isEmpty)
      None
    else
      Some(func -> cycle.toSet)
  }
}
