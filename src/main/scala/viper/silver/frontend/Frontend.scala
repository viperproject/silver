/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.frontend

import java.nio.file.{Files, Path}
import org.slf4j.LoggerFactory
import ch.qos.logback.classic.Logger
import scala.io.Source
import viper.silver.ast._
import viper.silver.reporter.{NoopReporter, Reporter}
import viper.silver.verifier._


/** Represents one phase of a frontend */
case class Phase(name: String, action: () => Unit)

/** A translator for some programming language that produces a Viper program (which then in turn can be verified using a
  * Viper verifier).
  *
  */
trait Frontend {

  /** Initialize this translator with a given verifier. Only meant to be called once. */
  def init(verifier: Verifier)

  /**
    * Reset the translator, and set the input program. Can be called many times to verify multiple programs
    * using the same verifier.
    */
  def reset(input: Seq[Path])

  /**
    * Reset any messages recorded internally (errors from previous program translations, etc.)
    */
  def resetMessages()

  /**
    * Reporter is the message interface which enables dynamic feedback from the backend.
    *
    * The reporter object can be passed as an argument of the Frontend implementation's constructor.
    *
    * The default implementation [[viper.silver.reporter.NoopReporter]] will simply swallow all
    * received messages.
    *
    * See https://bitbucket.org/viperproject/viperserver/src for more details.
    */
  val reporter: Reporter = NoopReporter

  /**
    * Run the verification on the input and return the result.  This is equivalent to calling all the phases and then
    * returning result.
    */
  def run(): VerificationResult = {
    phases.foreach(p => p.action())
    result
  }

  /** The phases of this frontend which have to be executed in the order given by the list. */
  val phases: Seq[Phase]

  /**
    * The result of the verification attempt (only available after parse, typecheck, translate and
    * verify have been called).
    */
  def result: VerificationResult

  val logger: Logger = LoggerFactory.getLogger(getClass.getName).asInstanceOf[Logger]
}

trait SinglePhase extends Frontend {
  val phases = List(
    Phase("singlePhase", runPhase)
  )

  def runPhase()
}

trait DefaultPhases extends Frontend {

  val phases = List(
    Phase("parse", parse),
    Phase("typecheck", typecheck),
    Phase("translate", translate),
    Phase("verify", verify))

  /** Parse the program. */
  def parse()

  /** Type-check the program. */
  def typecheck()

  /** Translate the program to Viper. */
  def translate()

  /** Verify the Viper program using the verifier. */
  def verify()

}

trait SingleFileFrontend {
  def reset(file: Path)

  def reset(files: Seq[Path]) {
    files match {
      case f :: Nil => reset(f)
      case _ => sys.error("This frontend can only handle single files.")
    }
  }
}

/** A default implementation of a translator that keeps track of the state of the translator.
  */
trait DefaultFrontend extends Frontend with DefaultPhases with SingleFileFrontend {

  sealed trait Result[+A]

  case class Succ[+A](a: A) extends Result[A]

  case class Fail(errors: Seq[AbstractError]) extends Result[Nothing]

  protected type ParserResult <: AnyRef
  protected type TypecheckerResult <: AnyRef

  protected var _state: TranslatorState.Value = TranslatorState.Initial
  protected var _verifier: Option[Verifier] = None
  protected var _input: Option[String] = None
  protected var _inputFile: Option[Path] = None
  protected var _errors: Seq[AbstractError] = Seq()
  protected var _verificationResult: Option[VerificationResult] = None
  protected var _parseResult: Option[ParserResult] = None
  protected var _typecheckResult: Option[TypecheckerResult] = None
  protected var _program: Option[Program] = None

  def parserResult: ParserResult = _parseResult.get

  def typecheckerResult: TypecheckerResult = _typecheckResult.get

  def translatorResult: Program = _program.get

  def state = _state
  def errors = _errors
  def program = _program

  def setState(new_state: TranslatorState.Value): Unit = {
    _state = new_state
  }

  def setVerificationResult(ver_result: VerificationResult): Unit = {
    _verificationResult = Some(ver_result)
  }

  def getVerificationResult: Option[VerificationResult] = _verificationResult

  override def init(verifier: Verifier) {
    _state = TranslatorState.Initialized
    _verifier = Some(verifier)
  }

  override def reset(input: Path) {
    if (state < TranslatorState.Initialized) sys.error("The translator has not been initialized.")
    _state = TranslatorState.InputSet
    _inputFile = Some(input)
    _input = Some(Source.fromInputStream(Files.newInputStream(input)).mkString)
    _errors = Seq()
    _program = None
    _verificationResult = None
    _parseResult = None
    _typecheckResult = None
    resetMessages()
  }

  protected def mapVerificationResult(in: VerificationResult): VerificationResult

  protected def doParse(input: String): Result[ParserResult]

  protected def doTypecheck(input: ParserResult): Result[TypecheckerResult]

  protected def doTranslate(input: TypecheckerResult): Result[Program]

  override def parse() {
    if (state < TranslatorState.InputSet) sys.error("The translator has not been initialized, or there is no input set.")
    if (state >= TranslatorState.Parsed) return

    doParse(_input.get) match {
      case Succ(r) => _parseResult = Some(r)
      case Fail(e) => _errors ++= e
    }
    _state = TranslatorState.Parsed
  }

  override def typecheck() {
    // typecheck and translate (if successful)
    if (state >= TranslatorState.Typechecked || _errors.nonEmpty) return
    parse()
    if (_errors.nonEmpty) {
      _state = TranslatorState.Typechecked
      return
    }
    doTypecheck(_parseResult.get) match {
      case Succ(r) => _typecheckResult = Some(r)
      case Fail(e) => _errors ++= e
    }
    _state = TranslatorState.Typechecked
  }

  override def translate() {
    if (state >= TranslatorState.Translated || _errors.nonEmpty) return
    typecheck()
    if (_errors.nonEmpty) {
      _state = TranslatorState.Translated
      return
    }
    doTranslate(_typecheckResult.get) match {
      case Succ(r) => _program = Some(r)
      case Fail(e) => _errors ++= e
    }

    _state = TranslatorState.Translated
  }

  override def verify() {
    if (state >= TranslatorState.Verified || _errors.nonEmpty) return
    translate()
    if (_errors.nonEmpty) {
      _state = TranslatorState.Verified
      return
    }

    doVerify()
  }

  def doVerify() {
    _verificationResult = Some(mapVerificationResult(_verifier.get.verify(_program.get)))
    assert(_verificationResult != null)

    //    _verifier.get.stop()
    _state = TranslatorState.Verified
  }

  override def result = {
    if (_errors.isEmpty) {
      require(state >= TranslatorState.Verified)
      _verificationResult.get
    }
    else {
      Failure(_errors)
    }
  }
}

object TranslatorState extends Enumeration {
  type TranslatorState = Value
  val Initial, Initialized, InputSet, Parsed, Typechecked, Translated, Verified = Value
}
