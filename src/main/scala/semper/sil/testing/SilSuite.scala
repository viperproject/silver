package semper.sil.testing

import java.nio.file._
import semper.sil.verifier._
import semper.sil.ast.{TranslatedPosition, SourcePosition}
import semper.sil.frontend.Frontend

/**
 * A test suite for verification toolchains that use SIL.
 *
 * @author Stefan Heule
 */
abstract class SilSuite extends AnnotationBasedTestSuite {
  /** The list of verifiers to be used. */
  def verifiers: Seq[Verifier]

  /** The frontend to be used. */
  def frontend(verifier: Verifier, files: Seq[Path]): Frontend

  def systemsUnderTest: Seq[SystemUnderTest] =
   verifiers.map(VerifierUnderTest)

  private case class VerifierUnderTest(verifier: Verifier)
    extends SystemUnderTest with TimingUtils {

    val projectName: String = verifier.name

    def run(input: AnnotatedTestInput): Seq[AbstractOutput] = {
      val fe = frontend(verifier, input.files)
      val tPhases = fe.phases.map { p =>
        time(p.action)._2 + " (" + p.name + ")"
      }.mkString(", ")
      info(s"Verifier used: ${verifier.name} ${verifier.version}.")
      info(s"Time required: $tPhases.")
      val actualErrors = fe.result match {
        case Success => Nil
        case Failure(es) => es
      }
      actualErrors.map(SilOutput)
    }
  }
}

/**
 * Simple adapter for outputs produced by the SIL toolchain, i.e.,
 * [[semper.sil.verifier.AbstractError]]s.
 *
 * The advantage is that it allows [[semper.sil.testing.AbstractOutput]]
 * to be independent from the SIL AST.
 *
 * @param error the error produced by the SIL toolchain.
 */
case class SilOutput(error: AbstractError) extends AbstractOutput {
  def isSameLine(file: Path, lineNr: Int): Boolean = error.pos match {
    case p: SourcePosition => lineNr == p.line
    case p: TranslatedPosition => file == p.file && lineNr == p.line
    case _ => false
  }

  def fullId: String = error.fullId

  override def toString: String = error.toString
}

trait TimingUtils {
  /** Formats a time in milliseconds. */
  def formatTime(millis: Long): String = {
    if (millis > 1000) "%.2f sec".format(millis * 1.0 / 1000)
    else "%s msec".format(millis.toString)
  }

  /**
   * Measures the time it takes to execute `f` and returns the result of `f`
   * as well as the required time.
   */
  def time[T](f: () => T): (T, String) = {
    val start = System.currentTimeMillis()
    val r = f.apply()

    (r, formatTime(System.currentTimeMillis() - start))
  }
}