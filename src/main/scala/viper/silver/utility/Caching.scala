// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import java.security.MessageDigest

import viper.silver.ast.pretty.FastPrettyPrinter
import viper.silver.ast.Node

import scala.collection.mutable
import scala.language.postfixOps

trait DependencyAware {

  import viper.silver.ast._

  val dependencyHashMap: Map[Method, String]

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
            if (!marker.contains(func)) {
              markSubAST(func, marker)
              Seq(func) ++ getDependenciesRec(p, func.pres ++ func.posts ++ extractOptionalNode(func.body), marker)
            } else Nil
          case pred_access: PredicateAccess =>
            val pred = p.findPredicate(pred_access.predicateName)
            if (!marker.contains(pred)) {
              markSubAST(pred, marker)
              Seq(pred) ++ getDependenciesRec(p, extractOptionalNode(pred.body), marker)
            } else Nil
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
    val marker: mutable.Set[Hashable] = mutable.Set.empty
    markSubAST(m, marker)
    Seq(m) ++ p.domains ++ p.fields ++
      (m.pres ++ m.posts ++ m.body.toSeq).flatMap {
        n => n.deepCollect {
          case method_call: MethodCall =>
            val method = p.findMethod(method_call.methodName)
            if (!marker.contains(method)) {
              method.formalArgs ++ method.formalReturns ++
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
    val node = prefix + s"_<${astNode.getClass.toString()}>_" + FastPrettyPrinter.pretty(astNode)
    CacheHelper.buildHash(node)
  }
}
