// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.frontend

import java.nio.file.{Files, Path}

import org.slf4j.LoggerFactory
import ch.qos.logback.classic.Logger

import scala.io.Source
import viper.silver.ast._
import viper.silver.reporter.{Reporter, StdIOReporter}
import viper.silver.verifier._


/** Represents one phase of a frontend */
case class Phase(name: String, action: () => Unit)

/** A translator for some programming language that produces a Viper program (which then in turn can be verified using a
  * Viper verifier).
  *
  */
trait Frontend {

  /** Initialize this translator with a given verifier. Only meant to be called once. */
  protected def init(verifier: Verifier)

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
    * Reporter is the message interface which enables (potentially dynamic) feedback from the backend.
    *
    * The reporter object can be passed as an argument of the Frontend implementation's constructor.
    *
    * The default implementation [[viper.silver.reporter.StdIOReporter]] will print the reported messages to STDOUT.
    *
    * @see <a href="https://bitbucket.org/viperproject/viperserver/src">ViperServer</a> for more details.
    */
  val reporter: Reporter = StdIOReporter()

  /**
    * Run the verification on the input and return the result.  This is equivalent to calling all the phases and then
    * returning result.
    */
  def run(): VerificationResult = {
    phases.foreach(_.action())
    result
  }

  private def isValidPhase(phaseName: String) =
    if (!phases.exists(_.name == phaseName))
      sys.error(s"Phase $phaseName does not exist")

  def runOnly(phaseName: String) = {
    isValidPhase(phaseName)
    val index = phases.indexWhere(_.name == phaseName)
    phases(index).action()
  }

  def runTo(phaseName: String) = {
    isValidPhase(phaseName)
    val index = phases.indexWhere(_.name == phaseName) + 1
    phases.slice(0, index).foreach(_.action())
  }

  /** The phases of this frontend which have to be executed in the order given by the list. */
  val phases: Seq[Phase]

  /**
    * The result of the verification attempt (only available after parse, typecheck, translate and
    * verify have been called).
    */
  def result: VerificationResult

  /* ATG: the following field is used in ViperServer and should stay public for now. */
  val logger = LoggerFactory.getLogger(getClass.getName).asInstanceOf[Logger]
}

trait DefaultPhases extends Frontend {

  val phases = Seq(Phase("Parsing",           parsing _),
                   Phase("Semantic Analysis", semanticAnalysis _),
                   Phase("Translation",       translation _),
                   Phase("Consistency Check", consistencyCheck _),
                   Phase("Verification",      verification _))

  /** Parse the program. */
  def parsing()

  /** Perform semantic analysis in the program, such as type, names and scope checking. */
  def semanticAnalysis()

  /** Translate the program to Viper. */
  def translation()

  /** Perform a consistency check in Viper AST. */
  def consistencyCheck()

  /** Verify the Viper program using a verifier. */
  def verification()
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

/** A default implementation of a frontend that keeps track of the state of the verification. */
trait DefaultFrontend extends Frontend with DefaultPhases with SingleFileFrontend {

  sealed trait Result[+A]

  case class Succ[+A](a: A) extends Result[A]

  case class Fail(errors: Seq[AbstractError]) extends Result[Nothing]

  protected type ParsingResult <: AnyRef
  protected type SemanticAnalysisResult <: AnyRef

  protected var _state: DefaultStates.Value = DefaultStates.Initial
  protected var _verifier: Option[Verifier] = None
  protected var _input: Option[String] = None
  protected var _inputFile: Option[Path] = None
  protected var _errors: Seq[AbstractError] = Seq()
  protected var _parsingResult: Option[ParsingResult] = None
  protected var _semanticAnalysisResult: Option[SemanticAnalysisResult] = None
  protected var _verificationResult: Option[VerificationResult] = None
  protected var _program: Option[Program] = None

  /* ATG: The following two methods are needed in ViperServer. Please do not remove them. */
  def setState(new_state: DefaultStates.Value): Unit = {
    _state = new_state
  }

  def setVerificationResult(ver_result: VerificationResult): Unit = {
    _verificationResult = Some(ver_result)
  }

  def parsingResult: ParsingResult = _parsingResult.get

  def semanticAnalysisResult: SemanticAnalysisResult = _semanticAnalysisResult.get

  def translationResult: Program = _program.get

  def state = _state
  def errors = _errors
  def program = _program

  def getVerificationResult: Option[VerificationResult] = _verificationResult

  override def init(verifier: Verifier) {
    _state = DefaultStates.Initialized
    _verifier = Some(verifier)
  }

  override def reset(input: Path) {
    if (state < DefaultStates.Initialized) sys.error("The translator has not been initialized.")
    _state = DefaultStates.InputSet
    _inputFile = Some(input)
    _input = Some(Source.fromInputStream(Files.newInputStream(input)).mkString)
    _errors = Seq()
    _parsingResult = None
    _semanticAnalysisResult = None
    _verificationResult = None
    _program = None
    resetMessages()
  }

  protected def mapVerificationResult(in: VerificationResult): VerificationResult

  protected def doParsing(input: String): Result[ParsingResult]

  protected def doSemanticAnalysis(input: ParsingResult): Result[SemanticAnalysisResult]

  protected def doTranslation(input: SemanticAnalysisResult): Result[Program]

  protected def doConsistencyCheck(input: Program): Result[Program]

  override def parsing() = {
    if (state < DefaultStates.InputSet) sys.error("The translator has not been initialized, or there is no input set.")

    if (state == DefaultStates.InputSet) {
      doParsing(_input.get) match {
        case Succ(r) => _parsingResult = Some(r)
        case Fail(e) => _errors ++= e
      }
      _state = DefaultStates.Parsing
    }
  }

  override def semanticAnalysis() = {
    if (state == DefaultStates.Parsing && _errors.isEmpty) {
      doSemanticAnalysis(_parsingResult.get) match {
        case Succ(r) => _semanticAnalysisResult = Some(r)
        case Fail(e) => _errors ++= e
      }
      _state = DefaultStates.SemanticAnalysis
    }
  }

  override def translation() = {
    if (state == DefaultStates.SemanticAnalysis && _errors.isEmpty) {
      doTranslation(_semanticAnalysisResult.get) match {
        case Succ(r) => _program = Some(r)
        case Fail(e) => _errors ++= e
      }
      _state = DefaultStates.Translation
    }
  }

  override def consistencyCheck(): Unit = {
    if (state == DefaultStates.Translation && _errors.isEmpty) {
      doConsistencyCheck(_program.get) match {
        case Succ(program) => _program = Some(program)
        case Fail(errors)  => _errors ++= errors
      }
      _state = DefaultStates.ConsistencyCheck
    }
  }

  override def verification() = {
    if (state == DefaultStates.ConsistencyCheck && _errors.isEmpty) {

      _verificationResult = Some(mapVerificationResult(_verifier.get.verify(_program.get)))
      assert(_verificationResult.isDefined)
      _state = DefaultStates.Verification
    }
  }

  override def result: VerificationResult = {          _errors ++= errors

    if (_errors.isEmpty) {
      require(state >= DefaultStates.Verification)
      _verificationResult.get
    }
    else {
      Failure(_errors)
    }
  }
}

object DefaultStates extends Enumeration {
  val Initial, Initialized, InputSet, Parsing, SemanticAnalysis, Translation, ConsistencyCheck, Verification = Value
}
