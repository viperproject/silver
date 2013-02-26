package semper.source

import semper.sil.verifier.{VerificationResult, Verifier}
import java.io.File
import io.Source
import semper.sil.ast.Program

/** A translator for some programming language that produces a SIL program (which then in turn can be verified using a
  * SIL verifier).
  *
  * @author Stefan Heule
  */
trait Translator {

  /** Initialize this translator with a given verifier. */
  def init(verifier: Verifier)

  /** Reset the translator, and set the input program. */
  def reset(input: String)

  /** Reset the translator, and set the input program. */
  def reset(input: File) {
    reset(Source.fromFile(input).mkString)
  }

  /** Parse the program. */
  def parse()

  /** Type-check the program. */
  def typecheck()

  /** Translate the program to SIL. */
  def translate(): Program

  /** Verify the SIL program using the verifier. */
  def verify(): VerificationResult
}

/** A default implementation of a translator that keeps track of the state of the translator.
  */
trait DefaultTranslator extends Translator {

  private var _state: TranslatorState.Value = TranslatorState.Initial
  private var _verificationResult: VerificationResult = null
  private var _translationResult: Program = null
  private var _verifier: Verifier = null
  private var _input: String = null

  def state = _state

  def init(verifier: Verifier) {
    _state = TranslatorState.Initialized
    _verifier = verifier
  }

  def reset(input: String) {
    if (state < TranslatorState.InputSet) sys.error("The translator has not been initialized.")
    _state = TranslatorState.InputSet
    _input = input
  }

  protected def mapVerificationResult(in: VerificationResult): VerificationResult

  protected def doParse()

  protected def doTypecheck()

  protected def doTranslate(): Program

  override def parse() {
    if (state < TranslatorState.InputSet) sys.error("The translator has not been initialized, or there is no input set.")
    if (state >= TranslatorState.Parsed) return
    doParse()
  }

  override def typecheck() {
    if (state >= TranslatorState.Typechecked) return
    parse()
    doTypecheck()
  }

  override def translate(): Program = {
    if (state >= TranslatorState.Translated) return _translationResult
    typecheck()
    _translationResult = doTranslate()
    _translationResult
  }

  override def verify(): VerificationResult = {
    val program = translate()
    if (state >= TranslatorState.Verified) return _verificationResult
    _verificationResult = mapVerificationResult(_verifier.verify(program))
    _state = TranslatorState.Verified
    _verificationResult
  }
}

object TranslatorState extends Enumeration {
  type TranslatorState = Value
  val Initial, Initialized, InputSet, Parsed, Typechecked, Translated, Verified = Value
}
