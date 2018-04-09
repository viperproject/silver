/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.parser.PProgram
import viper.silver.verifier.{AbstractError, Failure, Success, VerificationResult}

/** Manage the loaded plugins and execute them during the different hooks (see [[viper.silver.plugin.SilverPlugin]]).
  *
  * The plugins will be executed in the order as specified when creating the manager.
  *
  * @param plugins The plugins to load.
  */
class SilverPluginManager(val plugins: Seq[SilverPlugin]) {

  protected var _errors: Seq[AbstractError] = Seq()
  def errors = _errors

  def foldWithError[T](start: T)(f: (T, SilverPlugin) => T): Option[T] ={
    var v: Option[T] = Some(start)
    plugins.foreach(plugin => {
      if (v.isDefined){
        val vprime = f(v.get, plugin)
        v = if (plugin.errors.isEmpty){
          Some(vprime)
        } else {
          _errors ++= plugin.errors
          None
        }
      }
    })
    v
  }

  def beforeParse(input: String, isImported: Boolean): Option[String] =
    foldWithError(input)((inp, plugin) => plugin.beforeParse(inp, isImported))

  def beforeResolve(input: PProgram): Option[PProgram] =
    foldWithError(input)((inp, plugin) => plugin.beforeResolve(inp))

  def beforeTranslate(input: PProgram): Option[PProgram] =
    foldWithError(input)((inp, plugin) => plugin.beforeTranslate(inp))

  def beforeMethodFilter(input: Program): Option[Program] =
    foldWithError(input)((inp, plugin) => plugin.beforeMethodFilter(inp))

  def beforeVerify(input: Program): Option[Program] =
    foldWithError(input)((inp, plugin) => plugin.beforeVerify(inp))

  def mapVerificationResult(input: VerificationResult): VerificationResult ={
    plugins.foldLeft(input)((inp, plugin) => plugin.mapVerificationResult(inp))
  }

  def beforeFinish(input: VerificationResult): VerificationResult ={
    plugins.foldLeft(input)((inp, plugin) => plugin.beforeFinish(inp))
  }

}

/** Provide a method to construct a [[viper.silver.plugin.SilverPluginManager]] from a string
  * (for example from a program argument).
  * The string contains one or more class names of plugins to load.
  * <br>
  * The names of different plugins can be separated by a colon (':').
  * The order of the plugins will be kept the same as in the string.
  * <br>
  * The plugins to load have to be on the classpath.
  * The name of the plugin should be the fully qualified name of the class.
  * Assuming two plugins called viper.silver.plugin.ARP and ch.ethz.inf.pm.SamplePlugin the SilverPluginManager
  * can be constructed as: {{{SilverPluginManager("viper.silver.plugin.ARP:ch.ethz.inf.pm.SamplePlugin")}}}
  */
object SilverPluginManager {

  def apply(pluginArg: Option[String]): SilverPluginManager =
    pluginArg match {
      case Some(plugins) =>
        new SilverPluginManager(resolveAll(plugins))
      case None =>
        new SilverPluginManager(Seq())
    }

  def resolveAll(pluginArg: String): Seq[SilverPlugin] =
    pluginArg.split(":").toSeq.map(resolve).filter(_.isDefined).map(_.get)

  def resolve(clazzName: String): Option[SilverPlugin] = {
    val clazz = try {
      Some(Class.forName(clazzName).newInstance())
    } catch {
      case e: ClassNotFoundException => None
    }
    clazz match {
      case Some(instance) if instance.isInstanceOf[SilverPlugin] =>
        Some(instance.asInstanceOf[SilverPlugin])
      case Some(instance) =>
        throw PluginWrongTypeException(instance.getClass.getName)
      case None =>
        throw PluginNotFoundException(clazzName)
    }
  }

  class PluginException extends Exception

  case class PluginNotFoundException(name: String) extends PluginException {
    override def toString: String = s"Plugin $name not found."
  }

  case class PluginWrongTypeException(name: String) extends PluginException {
    override def toString: String = s"Plugin $name has wrong type."
  }
}