/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.frontend

import fastparse.core.Parsed
import java.nio.file.{Path, Paths}

import org.apache.commons.io.FilenameUtils
import viper.silver.ast.{Node, Position, _}
import viper.silver.ast.utility.Consistency
import viper.silver.FastMessaging
import viper.silver.ast._
import viper.silver.parser._
import viper.silver.reporter.{OverallFailureMessage, OverallSuccessMessage}
import viper.silver.verifier._

import scala.collection.mutable

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
    reset(Paths.get(_config.file()))

    // run the parser, typechecker, and verifier
    verify()

    finish()
  }

  def setStartTime(): Unit ={
    _startTime = System.currentTimeMillis()
  }

  def finish(): Unit ={
    // print the result
    printFinishHeader()

    //TODO: eventually the functionality in the printSuccess and printErrors methods (and possibly other methods in this file)
    //TODO: could be factored out into the Reporter itself. For the moment, we interact with both functionality, for compatibility
    result match {
      case Success => {
        printSuccess();
        reporter.report(OverallSuccessMessage(System.currentTimeMillis() - _startTime))
      }
      case f@Failure(errors) => {
        printErrors(errors: _*);
        reporter.report(OverallFailureMessage(System.currentTimeMillis() - _startTime, f))
      }
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
    if(config.error.isEmpty && config.ideMode()) {
      loggerForIde.info(s"""{"type":"Start","backendType":"${_ver.name}"}\r\n""")
    }else {
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
        if(_config.ideMode()) {
          loggerForIde.info(s"""{"type":"End"}\r\n""")
        }else {
          logger.info(s"${_ver.name} finished.")
        }
      } else {
        printFinishHeaderWithTime()
      }
    }
  }

  protected def printFinishHeaderWithTime() {
    val timeMs = System.currentTimeMillis() - _startTime
    val time = f"${timeMs / 1000.0}%.3f seconds"
    if (_config.ideMode()) {
      loggerForIde.info(s"""{"type":"End","time":"$time"}\r\n""")
    } else {
      logger.info(s"${_ver.name} finished in $time.")
    }
  }

  protected def printErrors(errors: AbstractError*) {
    if (config.error.isEmpty && config.ideMode()) {
      //output a JSON representation of the errors for the IDE
      val ideModeErrors = errors.map(e => new IdeModeErrorRepresentation(e))
      val jsonErrors = ideModeErrors.map(e => e.jsonError).mkString(",")
      loggerForIde.info(s"""{"type":"Error","file":"${ideModeErrors.head.shortFileStr}","errors":[$jsonErrors]}""")
    } else {
      logger.info("The following errors were found:")

      errors.foreach(e => logger.info(s"  ${e.readableMessage}"))

      if (config.error.nonEmpty) {
        logger.info("")
        logger.info("Run with --help for usage and options")
      }
    }
  }

  protected def printOutline(program: Program) {
    if (config != null && config.ideMode()) {
      //output a JSON representation of the Outline for the IDE
      val members = program.members.map(m =>
        s"""{
           | "type": "${m.getClass.getName}",
           | "name": "${m.name}",
           | "location": "${m.pos.toString}"
        }""".stripMargin).mkString(",")

      loggerForIde.info(s"""{"type":"Outline","members":[$members]}""")
    }
  }

  case class Definition(name:String, typ: String, location: Position, scope: Option[AbstractSourcePosition] = None) {}

  private def addDecl(definitions: mutable.ListBuffer[Definition], typ: String, name: String, pos: Position,
                      enclosingNode: Node with Positioned) = enclosingNode.pos match {
      case position: AbstractSourcePosition =>
        definitions += Definition(name, typ, pos, Some(position))
      case _ =>
    }

  protected def printDefinitions(program: Program) {
    //This works, as the scope of all LocalVarDecls is the enclosing Member
    if (config != null && config.ideMode()) {
      val definitions = mutable.ListBuffer[Definition]()
      program.members.foreach {
        case t: Field =>
          definitions += Definition(t.name, "Field", t.pos) //global
        case t: Function =>
          definitions += Definition(t.name, "Function", t.pos)
          t.formalArgs.foreach(arg => addDecl(definitions, "Argument", arg.name, arg.pos, t))
        case t: Method =>
          definitions += Definition(t.name, "Method", t.pos)
          t.formalArgs.foreach(arg => addDecl(definitions, "Argument", arg.name, arg.pos, t))
          t.formalReturns.foreach(arg => addDecl(definitions, "Return", arg.name, arg.pos, t))
          //FIXME
          //t.locals.foreach(arg => addDecl(definitions, "Local", arg.name, arg.pos, t))
        case t: Predicate =>
          definitions += Definition(t.name, "Predicate", t.pos)
          t.formalArgs.foreach(arg => addDecl(definitions,"Argument", arg.name, arg.pos, t))
        case t: Domain =>
          definitions += Definition(t.name, "Domain", t.pos)
          t.functions.foreach(func => {
            definitions += Definition(func.name, "Function", func.pos)
            func.formalArgs.foreach(arg => addDecl(definitions, "Argument", arg.name, arg.pos, t))
          })
          t.axioms.foreach(axiom => addDecl(definitions, "Axiom", axiom.name, axiom.pos, t))
      }
      //output a JSON representation of the Outline for the IDE
      val defs = definitions.map(d =>
        s"""{
           |"type": "${d.typ}",
           |"name": "${d.name}",
           |"location": "${d.location.toString}",
           |"scopeStart": "${d.scope match {
              case Some(s) => s.start.line + ":" + s.start.column
              case _ => "global" }}",
           |"scopeEnd": "${d.scope match {
              case Some(s) if s.end.isDefined => s.end.get.line + ":" + s.end.get.column
              case _ => "global" }}",
        }""".stripMargin).mkString(",")

      loggerForIde.info(s"""{"type":"Definitions","definitions":[$defs]}""")
    }
  }

  protected def printSuccess() {
    if (config.ideMode()) {
      loggerForIde.info("""{"type":"Success"}""")
    } else {
      logger.info("No errors found.")
    }
  }

  override def doParse(input: String): Result[ParserResult] = {
    val file = _inputFile.get
    val result = FastParser.parse(input, file)

     result match {
      case Parsed.Success(e@ PProgram(_, _, _, _, _, _, _, err_list), _) =>
        if (err_list.isEmpty || err_list.forall(p => p.isInstanceOf[ParseWarning]))

        Succ({ e.initProperties(); e })
      else Fail(err_list)
      case Parsed.Failure(msg, next, extra) =>
        Fail(List(ParseError(msg.toString, SourcePosition(file, extra.line, extra.col))))
      case ParseError(msg, pos) => Fail(List(ParseError(msg, pos)))

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
        val enableFunctionTerminationChecks =
          config != null && config.verified && config.enableFunctionTerminationChecks()

        Translator(modifiedInput, enableFunctionTerminationChecks).translate match {
          case Some(program) =>
            val check = program.checkTransitively
            if(check.isEmpty) Succ(program) else Fail(check)

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
