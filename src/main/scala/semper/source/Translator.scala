package semper.source

import semper.sil.verifier.{Failure, AbstractError, VerificationResult, Verifier}
import java.io.File
import io.Source
import semper.sil.ast.Program

/** A translator for some programming language that produces a SIL program (which then in turn can be verified using a
  * SIL verifier).
  *
  * @author Stefan Heule
  */
trait Translator {

  /** Initialize this translator with a given verifier. Only meant to be called once. */
  def init(verifier: Verifier)

  /**
   * Reset the translator, and set the input program. Can be called many times to verify multiple programs
   * using the same verifier.
   */
  def reset(input: String)

  /** Reset the translator, and set the input program. */
  def reset(input: File) {
    reset(Source.fromFile(input).mkString)
  }

  /**
   * Run the verification on the input and return the result.  This is equivalent to calling parse, typecheck
   * translate, verify and then returning result.
   */
  def run(): VerificationResult = {
    parse()
    typecheck()
    translate()
    verify()
    result
  }

  /** Parse the program. */
  def parse()

  /** Type-check the program. */
  def typecheck()

  /** Translate the program to SIL. */
  def translate()

  /** Verify the SIL program using the verifier. */
  def verify()

  /**
   * The result of the verification attempt (only available after parse, typecheck, translate and
   * verify have been called).
   */
  def result: VerificationResult
}

/** A default implementation of a translator that keeps track of the state of the translator.
  */
trait DefaultTranslator extends Translator {

  sealed trait Result[+A]
  case class Succ[+A](a: A) extends Result[A]
  case class Fail(errors: Seq[AbstractError]) extends Result[Nothing]

  protected type ParserResult <: AnyRef
  protected type TypecheckerResult <: AnyRef

  protected var _state: TranslatorState.Value = TranslatorState.Initial
  protected var _verifier: Option[Verifier] = None
  protected var _input: Option[String] = None
  protected var _errors: Seq[AbstractError] = Seq()
  protected var _verificationResult: Option[VerificationResult] = None
  protected var _parseResult: Option[ParserResult] = None
  protected var _typecheckResult: Option[TypecheckerResult] = None
  protected var _program: Option[Program] = None

  def state = _state

  override def init(verifier: Verifier) {
    _state = TranslatorState.Initialized
    _verifier = Some(verifier)
  }

  override def reset(input: String) {
    if (state < TranslatorState.Initialized) sys.error("The translator has not been initialized.")
    _state = TranslatorState.InputSet
    _input = Some(input)
    _errors = Seq()
    _program = None
    _verificationResult = None
    _parseResult = None
    _typecheckResult = None
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
    if (state >= TranslatorState.Typechecked || !_errors.isEmpty) return
    parse()
    if (!_errors.isEmpty) {
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
    if (state >= TranslatorState.Translated || !_errors.isEmpty) return
    typecheck()
    if (!_errors.isEmpty) {
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
    if (state >= TranslatorState.Verified || !_errors.isEmpty) return
    translate()
    if (!_errors.isEmpty) {
      _state = TranslatorState.Verified
      return
    }
    _verificationResult = Some(mapVerificationResult(_verifier.get.verify(_program.get)))
    assert(_verificationResult != null)
    _state = TranslatorState.Verified
  }

  override def result = {
    require(state >= TranslatorState.Verified)
    if (_errors.isEmpty) _verificationResult.get
    else Failure(_errors)
  }
}

object TranslatorState extends Enumeration {
  type TranslatorState = Value
  val Initial, Initialized, InputSet, Parsed, Typechecked, Translated, Verified = Value
}
