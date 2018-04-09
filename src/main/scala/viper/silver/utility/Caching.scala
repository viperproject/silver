/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.utility

import java.security.MessageDigest

import viper.silver.ast.pretty.FastPrettyPrinter
import viper.silver.ast.{Member, Method, Node}

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
    * @return
    *          List of dependency [[Hashable]]s.
    */
  private def getDependenciesRec(p: Program, ns: Seq[Hashable]): List[Hashable] = {
    ns.flatMap {
      n => n.deepCollect {
        case func_app: FuncApp =>
          val func = p.findFunction(func_app.funcname)
          (func +: (getDependenciesRec(p, func.pres) ++ getDependenciesRec(p, func.posts))) ++ (func.body match {
            case Some(e: Exp) => getDependenciesRec(p, Seq(e))
            case _ => List()
          })
        case pred_access: PredicateAccess =>
          val pred = p.findPredicate(pred_access.predicateName)
          pred +: (pred.body match {
            case Some(e: Exp) => getDependenciesRec(p, Seq(e))
            case _ => List()
          })
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
    * @param p
    *          The [[Program]] under consideration.
    * @param m
    *          The [[Method]] for which the dependencies should be collected.
    * @return
    *          List of dependency [[Hashable]]s.
    */
  def getDependencies(p: Program, m: Method): List[Hashable] = p.domains ++ p.fields ++
  (m.pres ++ m.posts ++ m.body.toSeq).flatMap {
    n => n.deepCollect {
      case method_call: MethodCall =>
        val method = p.findMethod(method_call.methodName)
        method.formalArgs ++ method.formalReturns ++ method.pres ++ method.posts ++ getDependenciesRec(p, method.pres ++ method.posts)
      case func_app: FuncApp =>
        val function = p.findFunction(func_app.funcname)
        function +: getDependenciesRec(p, Seq(function))
      case pred_access: PredicateAccess =>
        val predicate = p.findPredicate(pred_access.predicateName)
        predicate +: getDependenciesRec(p, Seq(predicate))
    } flatten
  } toList
}

object CacheHelper {
  def buildHash(s:String): String = {
    new String(MessageDigest.getInstance("MD5").digest(s.getBytes))
  }
  def computeEntityHash(prefix: String, astNode: Node): String = {
    val node = prefix + "_" + FastPrettyPrinter.pretty(astNode)
    CacheHelper.buildHash(node)
  }
}
