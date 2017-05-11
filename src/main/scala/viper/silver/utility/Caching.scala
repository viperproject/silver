package viper.silver.utility

import java.security.MessageDigest

import viper.silver.ast.pretty.FastPrettyPrinter
import viper.silver.ast.{Member, Method, Node}

/**
  * Created by Neptun on 11.05.2017.
  */
class Caching {

}

trait DependencyAware{
  val dependencyHash: String

  //TODO: implement
  def getDependencies(m: Method): List[Member] = {
    List()
  }
}

object CacheHelper{
  def buildHash(s:String): String = {
    new String(MessageDigest.getInstance("MD5").digest(s.getBytes))
  }
  def computeEntityHash(prefix: String, astNode: Node): String = {
    val node = prefix + "_" + FastPrettyPrinter.pretty(astNode)
    CacheHelper.buildHash(node)
  }
}