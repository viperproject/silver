package semper.source

import semper.sil.verifier.{AbstractError, VerificationResult, Verifier}
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

  private var _state: TranslatorState.Value = TranslatorState.Initial
  private var _verificationResult: VerificationResult = null
  private var _program: Program = null
  private var _verifier: Verifier = null
  private var _input: String = null
  private var _errors: Seq[AbstractError] = Seq()

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
  }

  protected def mapVerificationResult(in: VerificationResult): VerificationResult

  protected def doParse(): Seq[AbstractError]

  protected def doTypecheck(): Seq[AbstractError]

  protected def doTranslate(): (Program, Seq[AbstractError])

  override def parse() {
    if (state < TranslatorState.InputSet) sys.error("The translator has not been initialized, or there is no input set.")
    if (state >= TranslatorState.Parsed) return
    _errors ++= doParse()
  }

  override def typecheck() {
    if (state >= TranslatorState.Typechecked) return
    parse()
    _errors ++= doTypecheck()
    _errors
  }

  override def translate() {
    if (state >= TranslatorState.Translated) return
    typecheck()
    val (p, e) = doTranslate()
    _state = TranslatorState.Translated
    _program = p
    _errors ++= e
  }

  override def verify() {
    if (state >= TranslatorState.Verified) return
    translate()
    _verificationResult = mapVerificationResult(_verifier.verify(_program))
    _state = TranslatorState.Verified
  }

  override def result = {
    require(state >= TranslatorState.Verified)
    _verificationResult
  }
}

object TranslatorState extends Enumeration {
  type TranslatorState = Value
  val Initial, Initialized, InputSet, Parsed, Typechecked, Translated, Verified = Value
}
