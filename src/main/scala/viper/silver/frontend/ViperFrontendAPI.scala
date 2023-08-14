package viper.silver.frontend

import viper.silver.ast.Program
import viper.silver.verifier.VerificationResult

import java.nio.file.Paths

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
      println("Not initialized")
    setStartingState()
    _program = Some(p)
    runAllPhases()
    result
  }

}
