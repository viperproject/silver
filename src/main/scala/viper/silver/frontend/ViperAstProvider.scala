package viper.silver.frontend


import ch.qos.logback.classic.Logger
import viper.silver.ast.Program
import viper.silver.logger.ViperStdOutLogger
import viper.silver.plugin.PluginAwareReporter
import viper.silver.reporter.Reporter
import viper.silver.verifier.{Success, VerificationResult, Verifier}


class ViperAstProvider(override val reporter: PluginAwareReporter,
                       override implicit val logger: Logger) extends SilFrontend {

  def this(reporter: Reporter, logger: Logger = ViperStdOutLogger("ViperAstProvider", "INFO").get) =
    this(PluginAwareReporter(reporter), logger)

  class Config(args: Seq[String]) extends SilFrontendConfig(args, "ViperAstProviderConfig") {
    verify()
  }

  class AstProvidingVerifier extends Verifier {
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
  }

  // Verification phase omitted
  override val phases = Seq(Parsing, SemanticAnalysis, Translation, ConsistencyCheck)

  // Since verification did not take place yet, there is currently nothing to finish.
  override def finish(): Unit = ()

  protected var instance: AstProvidingVerifier = _

  override def createVerifier(fullCmd: String): Verifier = {
    instance = new AstProvidingVerifier
    instance
  }

  override def configureVerifier(args: Seq[String]): SilFrontendConfig = {
    instance.parseCommandLine(args)
    instance.config
  }
}