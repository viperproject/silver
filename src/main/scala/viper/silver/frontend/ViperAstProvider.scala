package viper.silver.frontend


import ch.qos.logback.classic.Logger
import viper.silver.ast.Program
import viper.silver.logger.ViperStdOutLogger
import viper.silver.plugin.PluginAwareReporter
import viper.silver.reporter.{AstConstructionFailureMessage, AstConstructionSuccessMessage, Reporter}
import viper.silver.verifier.{Failure, Success, VerificationResult, Verifier}


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
    instance = new AstProvidingVerifier
    instance
  }

  override def configureVerifier(args: Seq[String]): SilFrontendConfig = {
    instance.parseCommandLine(args)
    instance.config
  }
}