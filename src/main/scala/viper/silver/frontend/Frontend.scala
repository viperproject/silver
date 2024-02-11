// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.frontend

import java.nio.file.Path

import org.slf4j.LoggerFactory
import ch.qos.logback.classic.Logger

import viper.silver.ast._
import viper.silver.ast.utility.{DiskLoader, FileLoader}
import viper.silver.reporter.StdIOReporter
import viper.silver.verifier._
import viper.silver.reporter.Reporter


/** A translator for some programming language that produces a Viper program (which then in turn can be verified using a
  * Viper verifier).
  *
  */
trait Frontend {

  /** Initialize this translator with a given verifier. Only meant to be called once. */
  protected def init(verifier: Verifier): Unit

  /**
    * Reset the translator, and set the input program. Can be called many times to verify multiple programs
    * using the same verifier.
    */
  def reset(input: Seq[Path]): Unit

  /**
    * Reset any messages recorded internally (errors from previous program translations, etc.)
    */
  def resetMessages(): Unit

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

  /** Represents a phase of the frontend */
  case class Phase(name: String, f: () => Unit)

  /** Phases of the frontend which executes sequentially. */
  val phases: Seq[Phase]

  /** Execute all phases of the frontend sequentially. */
  def runAllPhases(): Unit = {
    phases.foreach(ph => {
      logger.trace(s"Frontend: running phase ${ph.name}")
      ph.f()
    })
  }

  /** Executes only the specified phase of the frontend. The specified phase must a phase of the frontend.
    * Prerequisites must be met, like running previous phases successfully.
    * @param phase Phase to run. */
  def runOnly(phase: Phase): Unit = {
    assertPhase(phase)
    phase.f()
  }

  /** Executes each phase of the frontend, from the specified phase up to the last one. The specified phase must be a
    * phase of the frontend. Prerequisites must be met, like running phases prior to the specified one successfully.
    * @param phase First phase that will run. */
  def runFrom(phase: Phase): Unit = {
    runRange(phase, phases.last)
  }

  /** Executes each phase of the frontend, from the first phase up to the specified one. The specified phase must be a
    * phase of the frontend.
    * @param phase Last phase that will run. */
  def runTo(phase: Phase): Unit = {
    runRange(phases.head, phase)
  }

  /** Executes each phase in the range specified by a pair of phases. Both phases must be phases of the frontend.
    * Prerequisites must be met, like running phases prior to 'from' phase successfully.
    * @param from First phase from range that will run.
    * @param to   Last phase of range that will run. */
  def runRange(from: Phase, to: Phase): Unit = {
    assertPhase(from)
    assertPhase(to)
    phases.slice(phases.indexOf(from), phases.indexOf(to) + 1).foreach(_.f())
  }

  private def assertPhase(phase: Phase): Unit =
    assert(phases.contains(phase), s"The phase ${phase.name} is not one of the phases of the frontend")

  /**
    * The result of the verification attempt (only available after parse, typecheck, translate and
    * verify have been called).
    */
  def result: VerificationResult

  /* ATG: the following field is used in ViperServer and should stay public for now. */
  val logger = LoggerFactory.getLogger(getClass.getName).asInstanceOf[Logger]
}

trait DefaultPhases extends Frontend {

  val Parsing          = Phase("Parsing",           parsing _)
  val SemanticAnalysis = Phase("Semantic Analysis", semanticAnalysis _)
  val Translation      = Phase("Translation",       translation _)
  val ConsistencyCheck = Phase("Consistency Check", consistencyCheck _)
  val Verification     = Phase("Verification",      verification _)

  val phases = Seq(Parsing, SemanticAnalysis, Translation, ConsistencyCheck, Verification)

  /** Parse the program. */
  def parsing(): Unit

  /** Perform semantic analysis in the program, such as type, names and scope checking. */
  def semanticAnalysis(): Unit

  /** Translate the program to Viper. */
  def translation(): Unit

  /** Perform a consistency check in Viper AST. */
  def consistencyCheck(): Unit

  /** Verify the Viper program using a verifier. */
  def verification(): Unit
}

trait SingleFileFrontend {
  def reset(file: Path): Unit

  def reset(files: Seq[Path]): Unit = {
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
  protected var _loader: FileLoader = DiskLoader
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

  def translationResult: Program = _program match {
    case Some(p) => p
    case None =>
      val msg = "cannot extract translationResult: program is undefined"
      logger.error(msg)
      throw new NoSuchElementException(msg)
  }

  def state = _state
  def errors = _errors
  def pProgram = _parsingResult
  def saProgram = _semanticAnalysisResult
  def program = _program

  def getVerificationResult: Option[VerificationResult] = _verificationResult

  override def init(verifier: Verifier): Unit = {
    _state = DefaultStates.Initialized
    _verifier = Some(verifier)
  }

  override def reset(input: Path): Unit = {
    if (state < DefaultStates.Initialized) sys.error("The translator has not been initialized.")
    _state = DefaultStates.InputSet
    _inputFile = Some(input)
    _input = _loader.loadContent(input).toOption
    _errors = Seq()
    _parsingResult = None
    _semanticAnalysisResult = None
    _verificationResult = None
    _program = None
    resetMessages()
  }

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
      _verificationResult = Some(_verifier.get.verify(_program.get))
      assert(_verificationResult.isDefined)
      _state = DefaultStates.Verification
    }
  }

  override def result: VerificationResult = {

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
  type DefaultStates = Value
  val Initial, Initialized, InputSet, Parsing, SemanticAnalysis, Translation, ConsistencyCheck, Verification = Value
}
