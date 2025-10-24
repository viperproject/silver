// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import java.security.MessageDigest
import viper.silver.ast.pretty.FastPrettyPrinter
import viper.silver.ast.{Domain, DomainAxiom, DomainFunc, Node}

import scala.collection.mutable
import scala.language.postfixOps

trait DependencyAware {

  import viper.silver.ast._

  val dependencyHashMap: Map[Method, String]

  private def handleFunction(p: Program, marker: mutable.Set[Hashable], func: Function): Seq[Hashable] = {
    if (!marker.contains(func)) {
      markSubAST(func, marker)
      Seq(func) ++ getDependenciesRec(p, func.pres ++ func.posts ++ extractOptionalNode(func.body), marker)
    } else Nil
  }

  private def handlePredicate(p: Program, marker: mutable.Set[Hashable], pred: Predicate): Seq[Hashable] = {
    if (!marker.contains(pred)) {
      markSubAST(pred, marker)
      Seq(pred) ++ getDependenciesRec(p, extractOptionalNode(pred.body), marker)
    } else Nil
  }

  /**
    * Get the (irreflexive) transitive closure of dependencies of nodes from a list.
    *
    * @param p
    *          The [[Program]] under consideration.
    * @param ns
    *          The list of [[Hashable]] AST nodes for which the dependencies are collected.
    * @param marker
    *          The set of visited nodes. Needed to avoid infinite recursion and duplicates.
    * @return
    *          List of dependency [[Hashable]]s.
    */
  private def getDependenciesRec(p: Program, ns: Seq[Hashable], marker: mutable.Set[Hashable]): List[Hashable] = {
    ns.flatMap {
      n =>
        n.deepCollect {
          case func_app: FuncApp =>
            val func = p.findFunction(func_app.funcname)
            handleFunction(p, marker, func)
          case pred_access: PredicateAccess =>
            val pred = p.findPredicate(pred_access.predicateName)
            handlePredicate(p, marker, pred)
        } flatten
    } toList
  }

  private def getDependenciesInner(p: Program, m: Method, includeMethods: Boolean): List[Hashable] = {
    val marker: mutable.Set[Hashable] = mutable.Set.empty
    markSubAST(m, marker)
    Seq(m) ++ p.domains ++ p.fields ++
      (m.pres ++ m.posts ++ m.body.toSeq).flatMap {
        n => n.deepCollect {
          case method_call: MethodCall =>
            val method = p.findMethod(method_call.methodName)
            if (!marker.contains(method)) {
              (if(includeMethods) {getDependenciesInner(p, method, includeMethods)} else {Seq()}) ++ method.formalArgs ++ method.formalReturns ++
                method.pres ++ method.posts ++
                getDependenciesRec(p, method.formalArgs ++ method.formalReturns ++ method.pres ++ method.posts, marker)
            } else Nil
          case func_app: FuncApp =>
            getDependenciesRec(p, Seq(func_app), marker)
          case pred_access: PredicateAccess =>
            getDependenciesRec(p, Seq(pred_access), marker)
        } flatten
      } toList
  }

  /**
    * Find all (irreflexive) dependencies of the current method.
    *
    * This method is imprecise, but practical. Here's a list of known imprecisions:
    * - axioms are considered as global dependencies (even if they don't influence the method);
    * - fields are considered as global dependencies (even if they don't influence the method);
    * - concrete predicates used abstractly (w/o unfolding) bring transitive dependencies via their body.
    *
    * Danger! A bug in this method may lead to unsoundness caused by caching.
    *
    *
    * @param p
    *          The [[Program]] under consideration.
    * @param m
    *          The [[Method]] for which the dependencies should be collected.
    * @return
    *          List of dependency [[Hashable]]s.
    */
  def getDependencies(p: Program, m: Method): List[Hashable] = {
    getDependenciesInner(p, m, false)
  }

  /**
   * Same as `getDependencies`, but instead also collects all methods that are used transitively.
   * `getDependencies` is used for caching, which does not include transitively called
   * methods (only their pres, posts, etc.).
   *
   * `getDependenciesWithMethods` is instead used for the IDE functionality that allows to verify
   * a method or function at a specific source code location. In this case, we do want to also include
   * methods, so that we can form the transitive closure.
   */
  def getMethodDependenciesWithMethods(p: Program, m: Method): List[Hashable] = {
    getDependenciesInner(p, m, true)
  }

  def getFunctionDependencies(p: Program, f: Function): List[Hashable] = {
    val marker: mutable.Set[Hashable] = mutable.Set.empty
    handleFunction(p, marker, f) toList
  }

  private def markSubAST(node: Node, marker: mutable.Set[Hashable]): Unit = node.deepCollect {
    case n: Hashable => marker.add(n)
  }

  private def extractOptionalNode(bla: Option[Hashable]): Seq[Hashable] = bla match {
    case Some(n) => Seq(n)
    case None => Nil
  }
}

object CacheHelper {
  def buildHash(s:String): String = {
    new String(MessageDigest.getInstance("MD5").digest(s.getBytes))
  }
  def computeEntityHash(prefix: String, astNode: Node): String = {
    // orders subtrees of `astNode` when their ordering does not matter, i.e. a cache entry for a
    // similar node that just has a different ordering of its subtrees should be treated as a cache hit
    val normalizedAstNode = astNode match {
      case n: Domain =>
        Domain(n.name, n.functions.sorted, n.axioms.sorted, n.typVars)(n.pos, n.info, n.errT)
      case n => n
    }
    val node = prefix + s"_<${astNode.getClass.toString}>_" + FastPrettyPrinter.pretty(normalizedAstNode)
    CacheHelper.buildHash(node)
  }

  implicit def domainFnOrdering: Ordering[DomainFunc] = Ordering.by(FastPrettyPrinter.pretty(_))
  implicit def domainAxOrdering: Ordering[DomainAxiom] = Ordering.by(FastPrettyPrinter.pretty(_))
}
