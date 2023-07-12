// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.frontend

import viper.silver.ast.utility.Consistency
import viper.silver.ast._
import viper.silver.parser._
import viper.silver.plugin.SilverPluginManager
import viper.silver.plugin.SilverPluginManager.PluginException
import viper.silver.reporter._
import viper.silver.verifier._
import java.nio.file.{Path, Paths}
import viper.silver.FastMessaging

/**
 * Common functionality to implement a command-line verifier for Viper.  This trait
 * provides code to invoke the parser, parse common command-line options and print
 * error messages in a user-friendly fashion.
 */
case class MissingDependencyException(msg: String) extends Exception

trait SilFrontend extends DefaultFrontend {

  /**
   * Coarse-grained reasons only. Needed for generating appropriate exit codes for the entire application.
   * For fine-grained error reasons, @see [[VerificationResult]].
   */
  object ApplicationExitReason extends Enumeration {
    type PreVerificationFailureReasons = Value
    val UNKNOWN_EXIT_REASON            = Value(-2)
    val NOTHING_TO_BE_DONE             = Value(-1)
    val VERIFICATION_SUCCEEDED         = Value( 0) // POSIX standard
    val VERIFICATION_FAILED            = Value( 1)
    val COMMAND_LINE_ARGS_PARSE_FAILED = Value( 2)
    val ISSUE_WITH_PLUGINS             = Value( 3)
    val SYSTEM_DEPENDENCY_UNSATISFIED  = Value( 4)
  }

  protected var _appExitReason: ApplicationExitReason.Value = ApplicationExitReason.UNKNOWN_EXIT_REASON
  def appExitCode: Int = _appExitReason.id

  protected def specifyAppExitCode(): Unit = {
      if ( _state >= DefaultStates.Verification ) {
      _appExitReason = result match {
        case Success => ApplicationExitReason.VERIFICATION_SUCCEEDED
        case Failure(_) => ApplicationExitReason.VERIFICATION_FAILED
      }
    }
  }

  /**
   * Create the verifier. The full command is parsed for debugging purposes only,
   * since the command line arguments will be passed later on via
   * [[viper.silver.verifier.Verifier.parseCommandLine]].
   */
  def createVerifier(fullCmd: String): Verifier

  /** Configures the verifier by passing it the command line arguments ''args''.
    * Returns the verifier's effective configuration.
    */
  def configureVerifier(args: Seq[String]): SilFrontendConfig

  /** The Viper verifier to be used for verification (after it has been initialized). */
  def verifier: Verifier = _ver
  protected var _ver: Verifier = _

  override protected type ParsingResult = PProgram
  override protected type SemanticAnalysisResult = PProgram

  /** The current configuration. */
  protected var _config: SilFrontendConfig = _
  def config: SilFrontendConfig = _config

  /**
   * Default plugins are always activated and are run as last plugins.
   * All default plugins can be excluded from the plugins by providing the --disableDefaultPlugins flag
   */
  private val defaultPlugins: Seq[String] = Seq(
    "viper.silver.plugin.standard.adt.AdtPlugin",
    "viper.silver.plugin.standard.termination.TerminationPlugin",
    "viper.silver.plugin.standard.refute.RefutePlugin",
    "viper.silver.plugin.standard.predicateinstance.PredicateInstancePlugin"
  )
  /** For testing of plugin import feature */
  def defaultPluginCount: Int = defaultPlugins.size

  /** Name of the expected format for backend types. Examples: "Boogie", "SMTLIB". */
  def backendTypeFormat: Option[String] = None

  protected val fp = new FastParser()

  private var _plugins: SilverPluginManager = SilverPluginManager(defaultPlugins match {
    case Seq() => None
    case s => Some(s.mkString(":"))
  })(reporter, logger, _config, fp)

  def plugins: SilverPluginManager = _plugins

  protected var _startTime: Long = _
  def startTime: Time = _startTime

  def getTime: Long = System.currentTimeMillis() - _startTime

  def resetMessages(): Unit = {
    Consistency.resetMessages()
  }

  def setVerifier(verifier:Verifier): Unit = {
    _ver = verifier
  }

  def prepare(args: Seq[String]): Boolean = {

    reporter report CopyrightReport(_ver.signature)//${_ver.copyright}") // we agreed on 11/03/19 to drop the copyright

    /* Parse command line arguments and populate _config */
    parseCommandLine(args)

    /* Handle errors occurred while parsing of command-line options */
    if (_config.error.isDefined) {
      /* The command line arguments could not be parses. Hence, we should not
       * ready any arguments-related value from _config!
       */
      reporter report InvalidArgumentsReport(_ver.signature, List(CliOptionError(_config.error.get + ".")))
      _appExitReason = ApplicationExitReason.COMMAND_LINE_ARGS_PARSE_FAILED
      return false

    } else if (_config.exit) {
      /* Parsing succeeded, but the frontend should exit immediately never the less. */
      _appExitReason = ApplicationExitReason.NOTHING_TO_BE_DONE
      return false
    }

    // print dependencies if necessary
    if (_config.dependencies()) {
      reporter report ExternalDependenciesReport(_ver.dependencies)
    }
    true
  }

  /**
   * Main method that parses command-line arguments, parses the input file and passes
   * the Viper program to the verifier.  The resulting error messages (if any) will be
   * shown in a user-friendly fashion.
   */
  def execute(args: Seq[String]): Unit = {
    setStartTime()

    /* Create the verifier */
    _ver = createVerifier(args.mkString(" "))

    if (!prepare(args)) return

    // initialize the translator
    init(_ver)

    // set the file we want to verify
    try {
      reset(Paths.get(_config.file()))
    } catch {
      case exception: PluginException =>
        reporter report ExceptionReport(exception)
        _appExitReason = ApplicationExitReason.ISSUE_WITH_PLUGINS
        return
    }

    // Parse, type check, translate and verify
    try {
      runAllPhases()
      finish()
    }
    catch {
        case MissingDependencyException(msg) =>
          println("Missing dependency exception: " + msg)
          reporter report MissingDependencyReport(msg)
    }
  }

  override def reset(input: Path): Unit = {
    super.reset(input)

    if(_config != null) {

      // concat defined plugins and default plugins
      val pluginsArg: Option[String] = {
        val list = _config.plugin.toOption ++ defaultPlugins
        if (list.isEmpty) { None } else { Some(list.mkString(":")) }
      }
      _plugins = SilverPluginManager(pluginsArg)(reporter, logger, _config, fp)
    }
  }

  def setStartTime(): Unit = {
    _startTime = System.currentTimeMillis()
  }

  // TODO: do not hard code names of implementations into SilFrontend.
  def getVerifierName: String = {
    val silicon_pattern = raw"""(?i)(silicon)""".r
    val carbon_pattern = raw"""(?i)(carbon)""".r

    silicon_pattern.findFirstIn(verifier.name) match {
      case Some(_) =>
        "silicon"
      case _ =>
        carbon_pattern.findFirstIn(verifier.name) match {
          case Some(_) => "carbon"
          case _ => verifier.name
        }
    }
  }

  override def verification(): Unit = {
    def filter(input: Program): Result[Program]  = {
      plugins.beforeMethodFilter(input) match {
        case Some(inputPlugin) =>
          // Filter methods according to command-line arguments.
          val verifyMethods =
            if (config != null && config.methods() != ":all") Seq("methods", config.methods())
            else inputPlugin.methods map (_.name)

          val methods = inputPlugin.methods filter (m => verifyMethods.contains(m.name))
          val program = Program(inputPlugin.domains, inputPlugin.fields, inputPlugin.functions, inputPlugin.predicates, methods, inputPlugin.extensions)(inputPlugin.pos, inputPlugin.info, inputPlugin.errT)

          plugins.beforeVerify(program) match {
            case Some(programPlugin) => Succ(programPlugin)
            case None => Fail(plugins.errors)
          }

        case None => Fail(plugins.errors)
      }
    }

    if (state == DefaultStates.ConsistencyCheck && _errors.isEmpty) {
      filter(_program.get) match {
        case Succ(program) => _program = Some(program)
        case Fail(errors) => _errors ++= errors
      }
    }
    super.verification()
    _verificationResult = _verificationResult.map(plugins.mapVerificationResult(_program.get, _))
  }

  def finish(): Unit = {
    val tRes = result.transformedResult()
    val res = plugins.beforeFinish(tRes)
    _verificationResult = Some(res)
    res match {
      case Success =>
        reporter report OverallSuccessMessage(verifier.name, getTime)
      case f: Failure =>
        reporter report OverallFailureMessage(verifier.name, getTime, f)
    }
  }

  protected def parseCommandLine(args: Seq[String]): Unit = {
    _config = configureVerifier(args)
  }

  override def doParsing(input: String): Result[PProgram] = {
    val file = _inputFile.get
    plugins.beforeParse(input, isImported = false) match {
      case Some(inputPlugin) =>
        val result = fp.parse(inputPlugin, file, Some(plugins))
        if (result.errors.forall(p => p.isInstanceOf[ParseWarning])) {
          reporter report WarningsDuringParsing(result.errors)
          Succ({result.initProperties(); result})
        }
        else Fail(result.errors)
      case None => Fail(plugins.errors)
    }
  }

  override def doSemanticAnalysis(input: PProgram): Result[PProgram] = {
    plugins.beforeResolve(input) match {
      case Some(inputPlugin) =>
        val r = Resolver(inputPlugin)
        val analysisResult = r.run
        val warnings = for (m <- FastMessaging.sortmessages(r.messages) if !m.error) yield {
          TypecheckerWarning(m.label, m.pos)
        }
        if (warnings.nonEmpty)
          reporter report WarningsDuringTypechecking(warnings)
        analysisResult match {
          case Some(modifiedInput) =>
            Succ(modifiedInput)
          case None =>
            val errors = for (m <- FastMessaging.sortmessages(r.messages) if m.error) yield {
              TypecheckerError(m.label, m.pos)
            }
            Fail(errors)
        }

      case None => Fail(plugins.errors)
    }
  }

  override def doTranslation(input: PProgram): Result[Program] = {

    plugins.beforeTranslate(input) match {
      case Some(modifiedInputPlugin) =>
        Translator(modifiedInputPlugin).translate match {
          case Some(program) =>
            Succ(program)

          case None => // then there are translation messages
            Fail(FastMessaging.sortmessages(Consistency.messages) map (m => {
              TypecheckerError(m.label, m.pos)
            }))
        }

      case None => Fail(plugins.errors)
    }
  }

  def doConsistencyCheck(input: Program): Result[Program]= {
    var errors = input.checkTransitively
    if (backendTypeFormat.isDefined)
      errors = errors ++ Consistency.checkBackendTypes(input, backendTypeFormat.get)
    if (errors.isEmpty) {
      Succ(input)
    } else
      Fail(errors)
  }
}
