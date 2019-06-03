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

  /** Represents a phase of the frontend */
  case class Phase(name: String, f: () => Unit)

  /** Phases of the frontend which executes sequentially. */
  val phases: Seq[Phase]

  /** Execute all phases of the frontend sequentially. */
  def runAllPhases(): Unit = {
    phases.foreach(_.f())
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

class ReflectOfMe {
  def m(): Int = 5
  def n(i: Float): Int = 6

  import scala.reflect.runtime.universe.TypeTag
  import scala.reflect.runtime.universe.typeTag

  def getType[A : TypeTag](entity: A) =
    typeTag[A].tpe

  def runMN(): Unit = {
    // Check two things:
    // 1) If types are compatible (subtype, not identical) -> static (done)
    // 2) Downcast: If I can take the result from a method, assign to a Any var and cast it to next method call's param type. -> dynamic

    val runtime = scala.reflect.runtime.universe
    val mirror = runtime.runtimeMirror(getClass.getClassLoader)

    // Instance mirror
    val instanceMirror = mirror.reflect(this)
    val methodSymbol = mirror.typeOf[this.type].decl(runtime.TermName("m")).asMethod
    val methodMirror = instanceMirror.reflectMethod(methodSymbol)
    println(methodMirror)

    // Class mirror
    //val classSymbol = runtime.typeOf[this.type].typeSymbol.asClass
    //val classMirror = mirror.reflectClass(classSymbol)
    //val methodSymbol = mirror.typeOf[this.type].decl(runtime.TermName("m")).asMethod
    //val methodMirror = classMirror.re

    //val mTypeInfo = getType(m _)
    //println(mTypeInfo)
    //mTypeInfo.tpe

    // Execution
    val output = m()
    n(output)

    // 1) Type checking
    val outputType = getType(output)
    val inputType = getType(n _).typeArgs(0)
    //val inputType = getType(n _).paramLists

    val subclass: Boolean = outputType weak_<:< inputType
    println(subclass)

    // 2) Type casting
    val genericOutput: Any = output
//    val input = output.asInstanceOf[inputType]
  }
}

trait TestBase {
  // Result of a phase can be a data structure in case of success
  // or a list of error messages in case of failure.
  abstract class Result[A]
  case class Success[A](result: A) extends Result[A]
  case class Failure[Message](errors: Seq[Message]) extends Result[Nothing]

  object Phases extends Enumeration {
    type Phases = Value

    protected case class Phase[A, B](name: String, f: (A) => Result[B]) extends super.Val
  }

  def method(input: Char): Int = 3

  val phases = Seq.empty[Int]

//  val char: method.type
}

trait TestA {
  type PProgram <: Any
  type Program <: Any
  type Message <: Any

  abstract class Result[A]
  case class Success[A](result: A) extends Result[A]
  case class Failure[Message](errors: Seq[Message]) extends Result[Nothing]

  object Phases extends Enumeration {
    type Phases = Value

    protected case class Phase[A, B](name: String, f: (A) => Result[B]) extends super.Val

    val Parsing          = Phase("Parsing",           parsing _)
    val SemanticAnalysis = Phase("Semantic Analysis", semanticAnalysis _)
    val Translation      = Phase("Translation",       translation _)
    val ConsistencyCheck = Phase("Consistency Check", consistencyCheck _)
    val Verification     = Phase("Verification",      verification _)
  }

  // Verification phases
  val phases = Seq(
    Phases.Parsing,
//  Phases.SemanticAnalysis,
//  Phases.Translation,
//  Phases.ConsistencyCheck,
//  Phases.Verification
  )

  def parsing(program: String): Result[PProgram]
  def semanticAnalysis(program: PProgram): Result[PProgram]
  def translation(program: PProgram): Result[Program]
  def consistencyCheck(program: Program): Result[Program]
  def verification(program: Program): Result[Message]

  def run(program: String): Unit = {
    var x = "x".asInstanceOf[Phases.Parsing.name.type]
    var y = "x".asInstanceOf[Phases.Parsing.f.type]

//  var t = (x: Int) => x
//  2.isInstanceOf[t.type ]
    //var result = phases(0).f(program)
    //var result2 = phases(1).f(result)
  }

//def run(program: String): Unit = {
//  val result = parsing2(program)
//  result match {
//    case Right(p) => println(p)
//    case Left(errors) => errors.foreach(println)
//  }
//}

//def verify(program: String): Unit = { //Result[Message] = {
//  //Phases.Parsing.f(program.asInstanceOf[AnyRef])

//  var input: Any = program
//  phases.foreach(phase => {
//    phase.f(input) match {
//      case Success(result) => input = result
//      case Failure(errors) =>
//        errors.foreach(println)
//        return
//  }
//})
}

//def runAllPhases(): Unit = {
//  var program: String
//  phases.foldLeft(program)((input, phase) => phase.f(input))
//}
//}


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
  val Initial, Initialized, InputSet, Parsing, SemanticAnalysis, Translation, ConsistencyCheck, Verification = Value
}
