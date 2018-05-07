/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.frontend

import fastparse.core.Parsed
import java.nio.file.{Path, Paths}

import org.apache.commons.io.FilenameUtils
import viper.silver.ast.{Position, SourcePosition, _}
import viper.silver.ast.utility.Consistency
import viper.silver.FastMessaging
import viper.silver.ast._
import viper.silver.parser._
import viper.silver.plugin.SilverPluginManager
import viper.silver.plugin.SilverPluginManager.{PluginException, PluginNotFoundException, PluginWrongTypeException}
import viper.silver.verifier._

/**
 * Common functionality to implement a command-line verifier for Viper.  This trait
 * provides code to invoke the parser, parse common command-line options and print
 * error messages in a user-friendly fashion.
 */
trait SilFrontend extends DefaultFrontend {

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

  override protected type ParserResult = PProgram
  override protected type TypecheckerResult = Program

  /** The current configuration. */
  protected var _config: SilFrontendConfig = _
  def config = _config

  protected var _plugins: SilverPluginManager = SilverPluginManager(None)
  def plugins = _plugins

  protected var _startTime: Long = _
  def startTime = _startTime

  def resetMessages() {
    Consistency.resetMessages()
  }

  def setVerifier(verifier:Verifier): Unit ={
    _ver = verifier
  }

  def prepare(args: Seq[String]): Boolean ={

    /* Parse command line arguments and populate _config */
    parseCommandLine(args)

    /* Handle errors occurred while parsing of command-line options */
    if (_config.error.isDefined) {
      /* The command line arguments could not be parses. Hence, we should not
       * ready any arguments-related value from _config!
       */
      printFallbackHeader()
      printErrors(CliOptionError(_config.error.get + "."))
      return false
    } else if (_config.exit) {
      /* Parsing succeeded, but the frontend should exit immediately never the less. */
      printHeader()
      printFinishHeader()
      return false
    }

    printHeader()

    // print dependencies if necessary
    if (_config.dependencies()) {
      val s = (_ver.dependencies map (dep => {
        s"  ${dep.name} ${dep.version}, located at ${dep.location}."
      })).mkString("\n")
      logger.info("The following dependencies are used:")
      logger.info(s+"\n")
    }
    return true
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
        printFallbackHeader()
        printErrors(CliOptionError(exception.toString))
        return
    }

    // run the parser, typechecker, and verifier
    verify()

    finish()
  }


  override def reset(input: Path): Unit = {
    super.reset(input)

    if(_config != null) {
      // reset error messages of plugins
      _plugins = SilverPluginManager(_config.plugin.toOption)
    }
  }

  def setStartTime(): Unit = {
    _startTime = System.currentTimeMillis()
  }

  protected def getVerifierName: String = {
    val silicon_pattern = raw"""(?i)(silicon)""".r
    val carbon_pattern = raw"""(?i)(carbon)""".r

    silicon_pattern.findFirstIn(verifier.name) match {
      case Some(_) =>
        return "silicon"
      case _ =>
        carbon_pattern.findFirstIn(verifier.name) match {
          case Some(_) => "carbon"
          case _ => verifier.name
        }
    }
  }

  def finish(): Unit = {
    // print the result
    printFinishHeader()

    _plugins.beforeFinish(result) match {
      case Success =>
        printSuccess()
      case f@Failure(errors) =>
        printErrors(errors: _*)
    }
  }

  protected def parseCommandLine(args: Seq[String]) {
    _config = configureVerifier(args)
  }

  /** Prints a header that does **not** depend on any command line argument.
    * This method is thus safe to call even if parsing the command line
    * arguments failed.
    */
  protected def printFallbackHeader() {
    if(config.error.isDefined) {
      logger.info(s"${_ver.name} ${_ver.version}")
      logger.info(s"${_ver.copyright}\n")
    }
  }

  /** Prints the frontend header. May depend on command line arguments. */
  protected def printHeader() {
    printFallbackHeader()
  }

  /** Prints the final part of the frontend header. May depend on command line
    * arguments.
    */
  protected def printFinishHeader() {
    if (!_config.exit) {
      if (_config.noTiming()) {
        logger.info(s"${_ver.name} finished.")
      } else {
        printFinishHeaderWithTime()
      }
    }
  }

  protected def printFinishHeaderWithTime() {
    val timeMs = System.currentTimeMillis() - _startTime
    val time = f"${timeMs / 1000.0}%.3f seconds"
    logger.info(s"${_ver.name} finished in $time.")
  }

  protected def printErrors(errors: AbstractError*) {
    logger.info("The following errors were found:")

    errors.foreach(e => logger.info(s"  ${e.readableMessage}"))

    if (config != null && config.error.nonEmpty) {
      logger.info("")
      logger.info("Run with --help for usage and options")
    }
  }

  protected def printSuccess() = logger.info("No errors found.")

  override def doParse(input: String): Result[ParserResult] = {
    val file = _inputFile.get
    _plugins.beforeParse(input, isImported = false) match {
      case Some(inputPlugin) =>
        val result = FastParser.parse(inputPlugin, file, Some(_plugins))
          result match {
            case Parsed.Success(e@ PProgram(_, _, _, _, _, _, _, err_list), _) =>
              if (err_list.isEmpty || err_list.forall(p => p.isInstanceOf[ParseWarning]))
                Succ({ e.initProperties(); e })
              else Fail(err_list)
            case Parsed.Failure(msg, next, extra) => Fail(List(ParseError("Expected " + msg.toString, SourcePosition(file, extra.line, extra.col))))
            case ParseError(msg, pos) => Fail(List(ParseError(msg, pos)))
          }

      case None => Fail(_plugins.errors)
    }
  }

  /* TODO: Naming of doTypecheck and doTranslate isn't ideal.
           doTypecheck already translated the program, whereas doTranslate doesn't actually translate
           anything, but instead filters members.
   */

  override def doTypecheck(input: ParserResult): Result[TypecheckerResult] = {
    _plugins.beforeResolve(input) match {
      case Some(inputPlugin) =>
        val r = Resolver(inputPlugin)
        r.run match {
          case Some(modifiedInput) =>
            val enableFunctionTerminationChecks =
              config != null && config.verified && config.enableFunctionTerminationChecks()

            _plugins.beforeTranslate(modifiedInput) match {
              case Some(modifiedInputPlugin) =>
                Translator(modifiedInputPlugin, enableFunctionTerminationChecks).translate match {
                  case Some(program) =>
                    val check = program.checkTransitively
                    if (check.isEmpty) Succ(program) else Fail(check)

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

  override def doTranslate(input: TypecheckerResult): Result[Program] = {
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

  override def mapVerificationResult(in: VerificationResult): VerificationResult = _plugins.mapVerificationResult(in)

  private class IdeModeErrorRepresentation(val error: AbstractError) {
    private var fileOpt: Option[Path] = None
    private var startOpt: Option[HasLineColumn] = None
    private var endOpt: Option[HasLineColumn] = None

    /* Get the relevant error information from the error (if available) */
    error.pos match {
      case abs: AbstractSourcePosition =>
        fileOpt = Some(abs.file)
        startOpt = Some(abs.start)
        endOpt = abs.end
      case hlc: HasLineColumn =>
        startOpt = Some(hlc)
      case _: Position => /* Position gives us nothing to work with */
    }

    lazy val messageStr = extractMessage(error)
    lazy val escapedMessageStr = messageStr.
      replaceAll("\\\\","\\\\\\\\").
      replaceAll("\\\"","\\\\\"").
      replaceAll("\\n","\\\\n").
      replaceAll("\\r","\\\\r").
      replaceAll("\\t","\\\\t")
    lazy val longFileStr = fileOpt.map(_.toString).getOrElse("<unknown file>")
    lazy val shortFileStr = fileOpt.map(f => FilenameUtils.getName(f.toString)).getOrElse("<unknown file>")
    lazy val startStr = startOpt.map(toStr).getOrElse("<unknown start line>:<unknown start column>")
    lazy val endStr = endOpt.map(toStr).getOrElse("<unknown end line>:<unknown end column>")

    lazy val consoleErrorStr = s"$shortFileStr,$startStr: $messageStr"
    lazy val fileErrorStr = s"$longFileStr,$startStr,$endStr,$messageStr"

    lazy val jsonError =
      s"""{
         |"cached": ${error.cached},
         |"tag": "${error.fullId}",
         |"message": "$escapedMessageStr",
         |"start": "$startStr",
         |"end": "$endStr"
      }""".stripMargin

    @inline
    private def extractMessage(error: AbstractError) = {
      /* TODO: Disassembling readableMessage is just a fragile hack because AbstractError
       *       does not provide the "raw" error message.
       */
      error.readableMessage
           .replace(s"(${error.pos.toString})", "")
           .trim
    }

    @inline
    private def toStr(hlc: HasLineColumn) = s"${hlc.line}:${hlc.column}"
  }
}
