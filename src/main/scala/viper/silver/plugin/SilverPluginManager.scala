// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import ch.qos.logback.classic.Logger
import viper.silver.ast._
import viper.silver.frontend.SilFrontendConfig
import viper.silver.parser.PProgram
import viper.silver.reporter.Reporter
import viper.silver.verifier.{AbstractError, VerificationResult}

/** Manage the loaded plugins and execute them during the different hooks (see [[viper.silver.plugin.SilverPlugin]]).
  *
  * The plugins will be executed in the order as specified when creating the manager.
  *
  * @param plugins The plugins to load.
  */
class SilverPluginManager(val plugins: Seq[SilverPlugin]) {

  protected var _errors: Seq[AbstractError] = Seq()
  def errors: Seq[AbstractError] = _errors

  def foldWithError[T](start: T)(f: (T, SilverPlugin) => T): Option[T] = {
    plugins.foldLeft[Option[T]](Some(start)) {
      case (Some(nv), plugin) => {
        val vprime = f(nv, plugin)
        if (plugin.errors.isEmpty) {
          Some(vprime)
        } else {
          _errors ++= plugin.errors
          None
        }
      }
      case (None, _) => None
    }
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

  def apply(pluginArg: Option[String])
           (reporter: Reporter, logger: Logger, cmdArgs: SilFrontendConfig): SilverPluginManager =
    pluginArg match {
      case Some(plugins) =>
        new SilverPluginManager(resolveAll(plugins)(reporter, logger, cmdArgs))
      case None =>
        new SilverPluginManager(Seq())
    }

  def apply() = new SilverPluginManager(Seq())

  def resolveAll(pluginArg: String)
                (reporter: Reporter, logger: Logger, cmdArgs: SilFrontendConfig): Seq[SilverPlugin] =
    pluginArg.split(":").toSeq.map(resolve(_, reporter, logger, cmdArgs)).filter(_.isDefined).map(_.get)

  /** Tries to create an instance of the plugin class.
    *
    * The plugin constructor is expected to take either zero or three arguments (as specified in [[viper.silver.plugin.IOAwarePlugin]]):
    *  [[viper.silver.reporter.Reporter]],
    *  [[ch.qos.logback.classic.Logger]],
    *  [[viper.silver.frontend.SilFrontendConfig]].
    *
    * Example plugin class declarations:
    * <pre>
    * class MyPlugin(val _reporter: Reporter,
    *                val _logger: Logger,
    *                val _cmdArgs: SilFrontendConfig)
    *                extends IOAwarePlugin(_reporter, _logger, _cmdArgs) with SilverPlugin
    * </pre>
    * <pre>
    * class MyPlugin extends SilverPlugin
    * </pre>
    *
    * class TestPluginImport extends SilverPlugin
    *
    * @param clazzName The fully qualified name of the plugin class.
    * @param reporter  The reporter to be used in the plugin.
    * @param logger    The logger to be used in the plugin.
    * @param cmdArgs   The config object to be accessible from the plugin.
    *
    * @return A fresh instance of the plugin class
    *
    * @throws PluginNotFoundException  if the class is not found in the current environment.
    * @throws PluginWrongTypeException if the plugin class does not extend [[viper.silver.plugin.SilverPlugin]]
    * @throws PluginWrongArgsException if the plugin does not provide a constructor with the expected arguments.
    */
  def resolve(clazzName: String, reporter: Reporter, logger: Logger, cmdArgs: SilFrontendConfig): Option[SilverPlugin] = {
    val clazz = try {
      val constructor = Class.forName(clazzName).getConstructor(
        classOf[viper.silver.reporter.Reporter],
        classOf[ch.qos.logback.classic.Logger],
        classOf[viper.silver.frontend.SilFrontendConfig])
      Some(constructor.newInstance(reporter, logger, cmdArgs))
    } catch {
      case _: NoSuchMethodException =>
        try {
          Some(Class.forName(clazzName).getConstructor().newInstance())
        } catch {
          case _: NoSuchMethodException =>
            throw PluginWrongArgsException(clazzName)
        }
      case _: ClassNotFoundException =>
        None
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

  /** Tries to create an instance of the plugin class. Use this version only for testing and in contexts
    * where Silver's IO is not available.
    *
    * The plugin constructor is expected to take either zero arguments.
    *
    * Example plugin class declaration:
    * <pre>
    * class MyPlugin extends SilverPlugin
    * </pre>
    *
    * class TestPluginImport extends SilverPlugin
    *
    * @param clazzName The fully qualified name of the plugin class.
    *
    * @return A fresh instance of the plugin class
    *
    * @throws PluginNotFoundException  if the class is not found in the current environment.
    * @throws PluginWrongTypeException if the plugin class does not extend [[viper.silver.plugin.SilverPlugin]]
    * @throws PluginWrongArgsException if the plugin does not provide a constructor with no arguments.
    */
  def resolve(clazzName: String): Some[SilverPlugin] = {
    val clazz = try {
      Some(Class.forName(clazzName).getConstructor().newInstance())
    } catch {
      case _: NoSuchMethodException =>
        throw PluginWrongArgsException(clazzName)
      case _: ClassNotFoundException =>
        None
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

  case class PluginWrongArgsException(name: String) extends PluginException {
    override def toString: String = s"Plugin $name does not implement a constructor with the required signature."
  }
}