// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silver.frontend


import ch.qos.logback.classic.Logger
import viper.silver.ast.Program
import viper.silver.logger.ViperStdOutLogger
import viper.silver.plugin.SilverPluginManager
import viper.silver.reporter.{AstConstructionFailureMessage, AstConstructionSuccessMessage, Reporter}
import viper.silver.verifier.{Failure, Success, VerificationResult, Verifier}

import java.nio.file.Path


class ViperAstProvider(override val reporter: Reporter,
                       override implicit val logger: Logger = ViperStdOutLogger("ViperAstProvider", "INFO").get,
                       private val disablePlugins: Boolean = false) extends SilFrontend {

  class Config(args: Seq[String]) extends SilFrontendConfig(args, "ViperAstProviderConfig") {
    verify()
  }

  class AstProvidingVerifier(rep: Reporter) extends Verifier {
    private var _config: Config = _

    def config: Config = _config

    override def name = "Viper AST Constructor"

    override def version = ""

    override def buildVersion = ""

    override def copyright: String = "(c) Copyright ETH Zurich 2012 - 2020"

    override def signature: String = name

    override def debugInfo(info: Seq[(String, Any)]): Unit = {}

    override def dependencies: Seq[Nothing] = Nil

    override def start(): Unit = ()

    override def stop(): Unit = {}

    override def verify(program: Program): VerificationResult = Success

    override def parseCommandLine(args: Seq[String]): Unit = {
      _config = new Config(args)
    }

    override def reporter: Reporter = rep
  }

  // Verification phase omitted
  override val phases: Seq[Phase] = Seq(Parsing, SemanticAnalysis, Translation, ConsistencyCheck)

  override def result: VerificationResult = {

    if (_errors.isEmpty && _program.isDefined) {
      require(state >= DefaultStates.ConsistencyCheck)
      Success
    }
    else {
      Failure(_errors)
    }
  }

  override def finish(): Unit = {
    result match {
      case Success =>
        reporter report AstConstructionSuccessMessage(getTime)
      case f: Failure =>
        reporter report AstConstructionFailureMessage(getTime, f)
    }
  }

  protected var instance: AstProvidingVerifier = _

  override def createVerifier(fullCmd: String): Verifier = {
    instance = new AstProvidingVerifier(reporter)
    instance
  }

  override def configureVerifier(args: Seq[String]): SilFrontendConfig = {
    instance.parseCommandLine(args)
    instance.config
  }

  override def reset(input: Path): Unit = {
    super.reset(input)
    if (_config != null) {
      noPluginsManager = SilverPluginManager(None)(reporter, logger, _config, fp)
    }
  }

  private var noPluginsManager = SilverPluginManager(None)(reporter, logger, _config, fp)
  override def plugins: SilverPluginManager = {
    if (disablePlugins) noPluginsManager
    else {
      super.plugins
    }
  }
}