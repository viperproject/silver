// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.frontend

import viper.silver.ast.SourcePosition
import viper.silver.ast.utility.Consistency
import viper.silver.FastMessaging
import viper.silver.ast._
import viper.silver.parser._
import viper.silver.plugin.SilverPluginManager
import viper.silver.plugin.SilverPluginManager.PluginException
import viper.silver.reporter._
import viper.silver.verifier._
import fastparse.all.{Parsed, ParserInput}
import fastparse.all
import java.nio.file.{Path, Paths}


/**
 * Common functionality to implement a command-line verifier for Viper.  This trait
 * provides code to invoke the parser, parse common command-line options and print
 * error messages in a user-friendly fashion.
 */
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

  protected var _plugins: SilverPluginManager = SilverPluginManager()
  def plugins: SilverPluginManager = _plugins

  protected var _startTime: Long = _
  def startTime: Time = _startTime

  def getTime: Long = System.currentTimeMillis() - _startTime

  def resetMessages() {
    Consistency.resetMessages()
  }

  def setVerifier(verifier:Verifier): Unit = {
    _ver = verifier
  }

  def prepare(args: Seq[String]): Boolean = {

    reporter report CopyrightReport(s"${_ver.signature}\n")//${_ver.copyright}") // we agreed on 11/03/19 to drop the copyright

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
  def execute(args: Seq[String]) {
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
    run()

    finish()
  }


  override def reset(input: Path): Unit = {
    super.reset(input)

    if(_config != null) {
      // reset error messages of plugins
      _plugins = SilverPluginManager(_config.plugin.toOption)(reporter, logger, _config)
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

  def finish(): Unit = {
    _plugins.beforeFinish(result) match {
      case Success =>
        reporter report OverallSuccessMessage(verifier.name, getTime)
      case f: Failure =>
        reporter report OverallFailureMessage(verifier.name, getTime, f)
    }
  }

  protected def parseCommandLine(args: Seq[String]) {
    _config = configureVerifier(args)
  }

  override def doParsing(input: String): Result[PProgram] = {
    val file = _inputFile.get
    _plugins.beforeParse(input, isImported = false) match {
      case Some(inputPlugin) =>
        val result = FastParser.parse(inputPlugin, file, Some(_plugins))
          result match {
            case Parsed.Success(e@ PProgram(_, _, _, _, _, _, _, err_list), _) =>
              if (err_list.isEmpty || err_list.forall(p => p.isInstanceOf[ParseWarning])) {
                reporter report WarningsDuringParsing(err_list)
                Succ({e.initProperties(); e})
              }
              else Fail(err_list)
            case fail @ Parsed.Failure(_, index, extra) =>
              val msg = all.ParseError(fail.asInstanceOf[Parsed.Failure]).getMessage()
              val (line, col) = LineCol(extra.input.asInstanceOf[ParserInput], index)
              Fail(List(ParseError(s"Expected $msg", SourcePosition(file, line, col))))
            case error: ParseError => Fail(List(error))
          }

      case None => Fail(_plugins.errors)
    }
  }

  override def doSemanticAnalysis(input: PProgram): Result[PProgram] = {
    _plugins.beforeResolve(input) match {
      case Some(inputPlugin) =>
        val r = Resolver(inputPlugin)
        r.run match {
          case Some(modifiedInput) =>
            Succ(modifiedInput)
          case None =>
            val errors = for (m <- FastMessaging.sortmessages(r.messages)) yield {
              TypecheckerError(m.label, m.pos match {
                case fp: FilePosition =>
                  SourcePosition(fp.file, m.pos.line, m.pos.column)
                case _ =>
                  SourcePosition(_inputFile.get, m.pos.line, m.pos.column)
              })
            }
            Fail(errors)
        }

      case None => Fail(_plugins.errors)
    }
  }

  override def doTranslation(input: PProgram): Result[Program] = {

    _plugins.beforeTranslate(input) match {
      case Some(modifiedInputPlugin) =>
        Translator(modifiedInputPlugin).translate match {
          case Some(program) => Succ(program)

          case None => // then there are translation messages
            Fail(FastMessaging.sortmessages(Consistency.messages) map (m => {
              TypecheckerError(
                m.label, m.pos match {
                  case fp: FilePosition =>
                    SourcePosition(fp.file, m.pos.line, m.pos.column)
                  case _ =>
                    SourcePosition(_inputFile.get, m.pos.line, m.pos.column)
                })
            }))
        }

      case None => Fail(_plugins.errors)
    }
  }

  def doConsistencyCheck(input: Program): Result[Program]= {
    def filter(input: Program): Result[Program]  = {
      _plugins.beforeMethodFilter(input) match {
        case Some(inputPlugin) =>
          // Filter methods according to command-line arguments.
          val verifyMethods =
            if (config != null && config.methods() != ":all") Seq("methods", config.methods())
            else inputPlugin.methods map (_.name)

          val methods = inputPlugin.methods filter (m => verifyMethods.contains(m.name))
          val program = Program(inputPlugin.domains, inputPlugin.fields, inputPlugin.functions, inputPlugin.predicates, methods)(inputPlugin.pos, inputPlugin.info)

          _plugins.beforeVerify(program) match {
            case Some(programPlugin) => Succ(programPlugin)
            case None => Fail(_plugins.errors)
          }

        case None => Fail(_plugins.errors)
      }
    }

    val errors = input.checkTransitively
    if (errors.isEmpty)
      filter(input)
    else
      Fail(errors)
  }

  override def mapVerificationResult(in: VerificationResult): VerificationResult = _plugins.mapVerificationResult(in)
}
