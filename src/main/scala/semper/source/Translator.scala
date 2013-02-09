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
abstract class Translator(verifier: Verifier, input: String) {

  def parse()

  def typecheck()

  def translate(): Program

  def verify(): VerificationResult
}

/** A default implementation of a translator that keeps track of the state of the translator.
  *
  * @param verifier The verifier to be used.
  * @param input The program to be translated and verified.
  */
abstract class DefaultTranslator(verifier: Verifier, input: String) extends Translator(verifier, input) {

  private var _state: TranslatorState.Value = TranslatorState.Initial
  private var _verificationResult: VerificationResult = null
  private var _translationResult: Program = null

  def state = _state

  def this(verifier: Verifier, input: File) {
    this(verifier, Source.fromFile(input).mkString)
  }

  protected def mapVerificationResult(in: VerificationResult): VerificationResult

  protected def doParse()

  protected def doTypecheck()

  protected def doTranslate(): Program

  override def parse() {
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
    _verificationResult = mapVerificationResult(verifier.verify(program))
    _state = TranslatorState.Verified
    _verificationResult
  }
}

object TranslatorState extends Enumeration {
  type TranslatorState = Value
  val Initial, Parsed, Typechecked, Translated, Verified = Value
}
