/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.frontend

import java.io.File
import java.nio.file.{Path, Paths}

import fastparse.core.Parsed
import org.apache.commons.io.FilenameUtils
import viper.silver.FastMessaging
import org.rogach.scallop.exceptions.{Help, ScallopException, Version}
import viper.silver.parser._
import viper.silver.verifier._
import viper.silver.verifier.CliOptionError
import viper.silver.verifier.Failure
import viper.silver.verifier.ParseError
import viper.silver.ast.{AbstractSourcePosition, HasLineColumn, Position, Program, SourcePosition}
import viper.silver.verifier.TypecheckerError
import viper.silver.ast.utility.Consistency

/**
 * Common functionality to implement a command-line verifier for SIL.  This trait
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

  /** The SIL verifier to be used for verification (after it has been initialized). */
  def verifier: Verifier = _ver
  protected var _ver: Verifier = null

  override protected type ParserResult = PProgram
  override protected type TypecheckerResult = Program

  /** The current configuration. */
  protected var _config: SilFrontendConfig = null
  def config = _config

  protected var _startTime: Long = _
  def startTime = _startTime

  def resetMessages() {
    Consistency.resetMessages()
  }

  /**
   * Main method that parses command-line arguments, parses the input file and passes
   * the SIL program to the verifier.  The resulting error messages (if any) will be
   * shown in a user-friendly fashion.
   */
  def execute(args: Seq[String]) {
    _startTime = System.currentTimeMillis()

    /* Create the verifier */
    _ver = createVerifier(args.mkString(" "))

    /* Parse command line arguments and populate _config */
    parseCommandLine(args)

    /* Must be executed before reading any value from _config!
     * If parsing failed, _config.error should be defined afterwards.
     */
    initializeLazyScallopConfig()

    /* Handle errors occurred while parsing of command-line options */
    if (_config.error.isDefined) {
      /* The command line arguments could not be parses. Hence, we should not
       * try to ready any arguments-related value from _config!
       */
      printFallbackHeader()
      printErrors(CliOptionError(_config.error.get + "."))
      println()
      _config.printHelp()
      return
    } else if (_config.exit) {
      /* Parsing succeeded, but the frontend should exit immediately never the less. */
      printHeader()
      printFinishHeader()
      return
    }

    printHeader()

    // print dependencies if necessary
    if (_config.dependencies()) {
      val s = (_ver.dependencies map (dep => {
        s"  ${dep.name} ${dep.version}, located at ${dep.location}."
      })).mkString("\n")
      println("The following dependencies are used:")
      println(s)
      println()
    }

    // initialize the translator
    init(_ver)

    // set the file we want to verify
    reset(Paths.get(_config.file()))

    // run the parser, typechecker, and verifier
    verify()

    // print the result
    printFinishHeader()

    result match {
      case Success => printSuccess()
      case Failure(errors) => printErrors(errors: _*)
    }
  }

  protected def parseCommandLine(args: Seq[String]) {
    _config = configureVerifier(args)
  }

  protected def initializeLazyScallopConfig() {
    _config.initialize {
      case Version =>
        _config.exit = true
        println(_config.builder.vers.get)
      case Help(_) =>
        _config.exit = true
        _config.printHelp()
      case ScallopException(message) =>
        _config.exit = true
        _config.error = Some(message)
    }
  }

  /** Prints a header that does **not** depend on any command line argument.
    * This method is thus safe to call even if parsing the command line
    * arguments failed.
    */
  protected def printFallbackHeader() {
    println(s"${_ver.name} ${_ver.version}")
    println(s"${_ver.copyright}")
    println()
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
        println(s"${_ver.name} finished.")
      } else {
        printFinishHeaderWithTime()
      }
    }
  }

  protected def printFinishHeaderWithTime() {
    val timeMs = System.currentTimeMillis() - _startTime
    val time = f"${timeMs / 1000.0}%.3f seconds"
    println(s"${_ver.name} finished in $time.")
  }

  protected def printErrors(errors: AbstractError*) {
    if (config.ideMode()) {
      val ideModeErrors = errors.map(e => new IdeModeErrorRepresentation(e))

      println(s"The following errors were found in ${ideModeErrors.head.shortFileStr}:")

//      viper.silver.utility.Common.toFile(ideModeErrors.map(_.fileErrorStr).mkString("\n"),
//                                         new File(config.ideModeErrorFile()))

      ideModeErrors.foreach(e => println(s"  ${e.consoleErrorStr}"))
    } else {
      println("The following errors were found:")

      errors.foreach(e => println(s"  ${e.readableMessage}"))
    }
  }

  protected def printSuccess() {
    println("No errors found.")
  }

  /*override def doParse(input: String): Result[ParserResult] = {
    val file = _inputFile.get



    Parser.parse(input, file) match {
      case Parser.Success(e@ PProgram(_, _, _, _, _, _, err_list), _) =>
        if (err_list.isEmpty || err_list.forall{ case p => p.isInstanceOf[ParseWarning] })
          Succ({ e.initTreeProperties(); e })
        else Fail(err_list)
      case Parser.Failure(msg, next) =>
        Fail(List(ParseError(s"Failure: $msg", SourcePosition(file, next.pos.line, next.pos.column))))
      case Parser.Error(msg, next) =>
        Fail(List(ParseError(s"Error: $msg", SourcePosition(file, next.pos.line, next.pos.column))))
    }
  }*/
  override def doParse(input: String): Result[ParserResult] = {
    val file = _inputFile.get
//    FastParser._file = file
    //   sahil FastPArser.parse(input)
    val result = FastParser.parse(input, file)
     result match {
      case Parsed.Success(e@ PProgram(_, _, _, _, _, _, err_list), _) =>
        if (err_list.isEmpty || err_list.forall{ case p => p.isInstanceOf[ParseWarning] })
        Succ({ e.initTreeProperties(); e })
      else Fail(err_list)
      case Parsed.Failure(msg, next, extra) =>
        Fail(List(ParseError(s"Failure: $msg", SourcePosition(file, extra.line, extra.col))))

    }

  }




  /* TODO: Naming of doTypecheck and doTranslate isn't ideal.
           doTypecheck already translated the program, whereas doTranslate doesn't actually translate
           anything, but instead filters members.
   */

  override def doTypecheck(input: ParserResult): Result[TypecheckerResult] = {
    val r = Resolver(input)
    r.run match {
      case Some(modifiedInput) =>
        Translator(modifiedInput).translate match {
          case Some(program) =>
            Succ(program)

          case None => // then these are translation messages
            Fail(FastMessaging.sortmessages(Consistency.messages) map (m =>
              {
                TypecheckerError(
                // AS: note: m.label may not be the right field here, but I think it is - the interface changed.

                m.label, m.pos match {
                  /*case fp: FilePosition =>
                    SourcePosition(fp.file, m.pos.line, m.pos.column)*/
                  case fp: PFilePosition =>
                    SourcePosition(fp.file, m.pos.line, m.pos.column)
                  case _ =>
                    SourcePosition(_inputFile.get, m.pos.line, m.pos.column)
                })

              }))
        }

      case None =>
        val errors = for (m <- FastMessaging.sortmessages(r.messages)) yield {
          TypecheckerError(m.label, m.pos match {
            /*case fp: FilePosition =>
              SourcePosition(fp.file, m.pos.line, m.pos.column)*/
            case fp: PFilePosition =>
              SourcePosition(fp.file, m.pos.line, m.pos.column)
            case _ =>
              SourcePosition(_inputFile.get, m.pos.line, m.pos.column)
          })
        }
        Fail(errors)
    }
  }

  override def doTranslate(input: TypecheckerResult): Result[Program] = {
    // Filter methods according to command-line arguments.
    val verifyMethods =
      if (config != null && config.methods() != ":all") Seq("methods", config.methods())
      else input.methods map (_.name)

    val methods = input.methods filter (m => verifyMethods.contains(m.name))
    val program = Program(input.domains, input.fields, input.functions, input.predicates, methods)(input.pos, input.info)

    Succ(program)
  }

  override def mapVerificationResult(in: VerificationResult) = in

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
    lazy val longFileStr = fileOpt.map(_.toString).getOrElse("<unknown file>")
    lazy val shortFileStr = fileOpt.map(f => FilenameUtils.getName(f.toString)).getOrElse("<unknown file>")
    lazy val startStr = startOpt.map(toStr).getOrElse("<unknown start line>:<unknown start column>")
    lazy val endStr = endOpt.map(toStr).getOrElse("<unknown end line>:<unknown end column>")
    lazy val typeStr = error.fullId

    //lazy val consoleErrorStr = s"$shortFileStr,$startStr: $messageStr"
    lazy val consoleErrorStr = s"[$typeStr] $startStr: $messageStr"
    lazy val fileErrorStr = s"$longFileStr,$startStr,$endStr,$messageStr"

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
