package viper.silver.frontend

import viper.silver.ast.Program
import viper.silver.verifier.VerificationResult


/**
  * Trait that can be mixed into SilFrontends to make them easily usable by actual Viper frontends that do not use
  * Viper's parser, type checker, etc., but instead directly consistency-check and verify a Viper AST.
  * Compared to working directly with an instance of [[viper.silver.verifier.Verifier]], SilFrontend manages plugins
  * automatically.
  * To use it:
  * - create an instance f of a specific SilFrontend with ViperFrontendAPI mixed in
  * - call f.initialize(args), where args are the command line arguments without any file name.
  * - (potentially repeatedly) call f.verify(p), where p is the program to verify
  * - call f.stop() when done
  * Plugin usage must be managed via command line arguments.
  * Existing implementations are SiliconFrontendAPI and CarbonFrontendAPI
  */
trait ViperFrontendAPI extends SilFrontend {

  private var initialized = false
  override val phases: Seq[Phase] = Seq(ConsistencyCheck, Verification)
  val dummyInputFilename = "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver"

  def initialize(args: Seq[String]): Unit = {
    // create verifier
    // parse args on frontend, set on verifier
    val v = createVerifier(args.mkString(" "))
    setVerifier(v)
    _verifier = Some(v)
    parseCommandLine(args :+ "--ignoreFile" :+ dummyInputFilename)
    resetPlugins()
    initialized = true
  }

  protected def setStartingState() = {
    _state = DefaultStates.ConsistencyCheck
  }

  def verify(p: Program): VerificationResult = {
    if (!initialized)
      throw new IllegalStateException("Not initialized")
    setStartingState()
    _program = Some(p)
    runAllPhases()
    result
  }

  def stop(): Unit = {
    if (!initialized)
      throw new IllegalStateException("Not initialized")
    _verifier.foreach(_.stop())
  }

}

/**
  * Version of ViperFrontendAPI that skips the consistency check phase.
  */
trait MinimalViperFrontendAPI extends ViperFrontendAPI {
  override val phases: Seq[Phase] = Seq(Verification)

  override protected def setStartingState() = {
    _state = DefaultStates.ConsistencyCheck
  }
}
