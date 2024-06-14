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
  val API_HOST = "http://viper-server.inf.ethz.ch:10000"

  /** Whether program will be submitted to database */
  protected def allowSubmission: Boolean

  /** Plaintext Viper program that was verified */
  protected def program: String

  /** Frontend that generated program, if manually submitted to Silicon and Carbon this should be equal to [[originalVerifier]] */
  protected def originalFrontend: String

  /** Arguments passed to the verifier */
  protected def args: Array[String]

  /** Verifier used to verify program */
  protected def originalVerifier: String

  /** Was verification successful*/
  protected def succeeded: Boolean

  /** Time between verification start and end */
  protected def runtime: Long

  /** Sends program and metadata to viper-data-collection API */
  def submit(): Unit = {
    if (API_HOST != "" && allowSubmission) {
      val submission =
        Obj(
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

  def programToString(p: Program): String = FastPrettyPrinter.pretty(p)

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

/** To use when no [[SilFrontend]] is available.
  *
  * Methods to call before calling [[submit]]: [[setProgram]] and [[setSuccess]]
  */
class ManualProgramSubmitter(
    var allowSubmission: Boolean,
    var program: String,
    var originalFrontend: String,
    var originalVerifier: String,
    var args: Array[String]
) extends ProgramSubmitter {

  private val startTime: Long = System.currentTimeMillis()
  protected var succeeded: Boolean = false

  def setAllowSubmission(b: Boolean): Unit = allowSubmission = b

  def setProgram(p: String): Unit = program = p

  def setProgram(p: Program): Unit = program = programToString(p)

  def setSuccess(success: Boolean): Unit = succeeded = success

  override def runtime: Long = System.currentTimeMillis() - startTime
}

/** ProgramSubmitter that takes a [[SilFrontend]] to read out verification metrics, so they don't have to be manually defined.
  * Assumes submit will be called after verification is finished.
  */
trait FEProgramSubmitter extends ProgramSubmitter {

  var args: Array[String] = Array()

  /** Instance of frontend responsible for verification, used to read out verification metrics */
  protected val frontend: SilFrontend

  override def allowSubmission: Boolean =
    frontend.config.submitForEvaluation.getOrElse(false)

  override def originalFrontend: String = originalVerifier

  override def originalVerifier: String = frontend.getVerifierName.capitalize

  override def succeeded: Boolean = didVerSucceed(frontend.getVerificationResult)

  override def runtime: Long = frontend.getTime

  def setArgs(arguments: Array[String]): Unit = {
    args =
      arguments.filter(a => a != "--submitForEvaluation" && !a.endsWith(".vpr"))
  }
}

/** [[FEProgramSubmitter]] implementation that assumes program is available in local file.
  *
  * Methods to call before calling [[submit]]: [[setArgs]]
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

/** [[FEProgramSubmitter]] implementation that creates a submission from a program AST, for cases where no local file is available.
  *
  * Methods to call before calling [[submit]]: [[setProgram]] and [[setArgs]]
  */
class ViperProgramSubmitter(fe: SilFrontend) extends FEProgramSubmitter {
  private var viperProgram: Program = null
  protected val frontend = fe

  def setProgram(p: Program): Unit = {
    viperProgram = p
  }

  override def program: String = {
    if (viperProgram != null) {
      programToString(viperProgram)
    } else ""
  }

}
