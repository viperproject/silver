package viper.silver.utility

import scala.io.Source.fromFile
import ujson.{Arr, Obj}
import viper.silver.ast.Program
import viper.silver.ast.pretty.FastPrettyPrinter
import viper.silver.verifier.{Success, VerificationResult}
import viper.silver.frontend.{SilFrontend}

/** Trait for an object that submits a program to the viper-data-collection API */
trait ProgramSubmitter {

  /** Protocol, IP address and port of server hosting the viper-data-collection API */
  val API_HOST = "http://localhost:8080"

  /** Whether program will be submitted to database */
  protected def allowSubmission: Boolean

  /** Original filename of program to submit */
  protected def programName: String

  /** Plaintext Viper program that was verified */
  protected def program: String

  /** Frontend that generated program, if manually submitted to Silicon and Carbon this should be equal to [[originalVerifier]] */
  protected def originalFrontend: String

  /** Arguments passed to the verifier */
  protected def args: Array[String]

  /** Verifier used to verify program */
  protected def originalVerifier: String
  protected def succeeded: Boolean
  protected def runtime: Long

  /** Sends program and metadata to viper-data-collection API */
  def submit(): Unit = {
    if (API_HOST != "" && allowSubmission) {
      val submission =
        Obj(
          "originalName" -> programName,
          "program" -> program,
          "frontend" -> originalFrontend,
          "args" -> Arr.from[String](args),
          "originalVerifier" -> originalVerifier,
          "success" -> succeeded,
          "runtime" -> runtime
        )
      try {
        requests.post(s"$API_HOST/submit-program", data = submission)
      } catch {
        case _: Exception => println("Program couldn't be submitted")
      }
    }
  }

  protected def didVerSucceed(vr: Option[VerificationResult]): Boolean =
    vr match {
      case Some(res) =>
        res match {
          case Success => true
          case _       => false
        }
      case _ => false
    }
}

/** To use when no [[SilFrontend]] is available. [[setAllowSubmission]], [[setProgramInfo]] and [[setSuccess]] have to be called manually. */
class ManualProgramSubmitter extends ProgramSubmitter {

  private val startTime: Long = System.currentTimeMillis()
  protected var allowSubmission: Boolean = false
  protected var programName: String = ""
  protected var program: String = ""
  protected var originalFrontend: String = ""
  protected var args: Array[String] = Array()
  protected var originalVerifier: String = ""
  protected var succeeded: Boolean = false

  def setAllowSubmission(b: Boolean): Unit = allowSubmission = b

  def setProgramInfo(
      programName: String,
      args: Array[String],
      frontend: String,
      verifier: String
  ): Unit = {
    this.programName = programName
    this.args = args
    this.originalFrontend = frontend
    this.originalVerifier = verifier
  }

  def setProgram(p: String): Unit = program = p

  def setSuccess(success: Boolean): Unit = succeeded = success

  override def runtime: Long = System.currentTimeMillis() - startTime

}

/** ProgramSubmitter that takes a [[SilFrontend]] to read out verification metrics, so they don't have to be manually defined.
  * Assumes submit will be called after verification is finished.
  */
trait FEProgramSubmitter extends ProgramSubmitter {

  var args: Array[String] = Array()
  var programName = ""

  /** Instance of frontend responsible for verification, used to read out verification metrics */
  protected val frontend: SilFrontend

  override def allowSubmission: Boolean =
    frontend.config.submitForEvaluation.getOrElse(false)

  def originalFrontend: String = originalVerifier

  def originalVerifier: String = frontend.getVerifierName.capitalize

  def succeeded: Boolean = didVerSucceed(frontend.getVerificationResult)

  def runtime: Long = frontend.getTime

  def setArgs(arguments: Array[String]): Unit = {
    args =
      arguments.filter(a => a != "--submitForEvaluation" && !a.endsWith(".vpr"))
  }

  def setName(n: String): Unit = {
    programName = n
  }

  /** Converts metadata to JSON Obj and submits it to [[API_HOST]]/submit-program. Only submits if --submitForEvaluation
    * flag was passed.
    */
  override def submit(): Unit = {
    if (API_HOST != "" && allowSubmission) {
      val submission =
        Obj(
          "originalName" -> programName,
          "program" -> program,
          "frontend" -> originalFrontend,
          "args" -> Arr.from[String](args),
          "originalVerifier" -> originalVerifier,
          "success" -> succeeded,
          "runtime" -> runtime
        )
      try {
        requests.post(s"$API_HOST/submit-program", data = submission)
      } catch {
        case _: Exception => println("Program couldn't be submitted")
      }
    }
  }
}

/** [[FEProgramSubmitter]] implementation that assumes program is available in local file. Before submit() is valid to call,
  * setArgs() has to be called
  */
class FileProgramSubmitter(fe: SilFrontend) extends FEProgramSubmitter {

  private var programPath: String = ""
  protected val frontend: SilFrontend = fe

  override def program: String = {
    readFileContent(programPath)
  }

  override def setArgs(arguments: Array[String]): Unit = {
    programPath = arguments.find(_.endsWith(".vpr")) match {
      case Some(p) => p
      case None    => ""
    }
    setName(programPath.split("/").last)
    super.setArgs(arguments)
  }

  protected def readFileContent(file: String): String = {
    try {
      val fBuffer = fromFile(file)
      val content =
        try {
          fBuffer.mkString
        } catch {
          case _: Exception => ""
        } finally fBuffer.close()
      content
    } catch {
      case _: Exception => ""
    }
  }
}

/** [[FEProgramSubmitter]] implementation that creates a submission from a program AST, for cases where no local file is available. Before submit()
  * is valid to call, setProgram() and setArgs() have to be called.
  */
class ViperProgramSubmitter(fe: SilFrontend) extends FEProgramSubmitter {
  private var viperProgram: Program = null
  protected val frontend = fe

  def setProgram(p: Program): Unit = {
    viperProgram = p
  }

  override def program: String = {
    if (viperProgram != null) {
      FastPrettyPrinter.pretty(viperProgram)
    } else ""
  }

}
