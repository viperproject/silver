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
  protected var _program: Program = null
  protected var _verifier: Verifier = null
  protected var _input: String = null
  protected var _errors: Seq[AbstractError] = Seq()
  protected var _verificationResult: VerificationResult = null
  protected var _parseResult: ParserResult = null
  protected var _typecheckResult: TypecheckerResult = null

  def state = _state

  override def init(verifier: Verifier) {
    _state = TranslatorState.Initialized
    _verifier = verifier
  }

  override def reset(input: String) {
    if (state < TranslatorState.InputSet) sys.error("The translator has not been initialized.")
    _state = TranslatorState.InputSet
    _input = input
    _errors = Seq()
    _program = null
    _verificationResult = null
    _parseResult = null
    _typecheckResult = null
  }

  protected def mapVerificationResult(in: VerificationResult): VerificationResult

  protected def doParse(input: String): Result[ParserResult]

  protected def doTypecheck(input: ParserResult): Result[TypecheckerResult]

  protected def doTranslate(input: TypecheckerResult): Result[Program]

  override def parse() {
    if (state < TranslatorState.InputSet) sys.error("The translator has not been initialized, or there is no input set.")
    if (state >= TranslatorState.Parsed) return
    doParse(_input) match {
      case Succ(r) => _parseResult = r
      case Fail(e) => _errors ++= e
    }
    _state = TranslatorState.Parsed
  }

  override def typecheck() {
    if (state >= TranslatorState.Typechecked || !_errors.isEmpty) return
    parse()
    doTypecheck(_parseResult) match {
      case Succ(r) => _typecheckResult = r
      case Fail(e) => _errors ++= e
    }
    _state = TranslatorState.Typechecked
  }

  override def translate() {
    if (state >= TranslatorState.Translated || !_errors.isEmpty) return
    typecheck()
    doTranslate(_typecheckResult) match {
      case Succ(r) => _program = r
      case Fail(e) => _errors ++= e
    }
    _state = TranslatorState.Translated
  }

  override def verify() {
    if (state >= TranslatorState.Verified || !_errors.isEmpty) return
    translate()
    _verificationResult = mapVerificationResult(_verifier.verify(_program))
    assert(_verificationResult != null)
    _state = TranslatorState.Verified
  }

  override def result = {
    require(state >= TranslatorState.Verified)
    if (_errors.isEmpty) _verificationResult
    else Failure(_errors)
  }
}

object TranslatorState extends Enumeration {
  type TranslatorState = Value
  val Initial, Initialized, InputSet, Parsed, Typechecked, Translated, Verified = Value
}
