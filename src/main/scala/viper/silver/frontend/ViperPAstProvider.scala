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
import viper.silver.reporter.Reporter
import viper.silver.verifier.{Failure, Success, VerificationResult, Verifier}

import java.nio.file.Path


class ViperPAstProvider(override val reporter: Reporter,
                        override implicit val logger: Logger = ViperStdOutLogger("ViperPAstProvider", "INFO").get,
                        private val disablePlugins: Boolean = false) extends SilFrontend {

  class Config(args: Seq[String]) extends SilFrontendConfig(args, "ViperPAstProviderConfig") {
    verify()
  }

  class PAstProvidingVerifier(rep: Reporter) extends Verifier {
    private var _config: Config = _

    def config: Config = _config

    override def name = "Viper PAST Constructor"

    override def version = ""

    override def buildVersion = ""

    override def copyright: String = "(c) Copyright ETH Zurich 2012 - 2023"

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

  // All phases after semantic analysis omitted
  override val phases: Seq[Phase] = Seq(Parsing, SemanticAnalysis)

  override def result: VerificationResult = {

    if (_errors.isEmpty) {
      require(state >= DefaultStates.SemanticAnalysis)
      Success
    }
    else {
      Failure(_errors)
    }
  }

  protected var instance: PAstProvidingVerifier = _

  override def createVerifier(fullCmd: String): Verifier = {
    instance = new PAstProvidingVerifier(reporter)
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