/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.utility

import java.security.MessageDigest

import viper.silver.ast.pretty.FastPrettyPrinter
import viper.silver.ast.{Member, Method, Node}

trait DependencyAware {
  val dependencyHash: String

  //TODO: implement
  def getDependencies(m: Method): List[Member] = {
    List()
  }
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