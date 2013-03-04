package semper.sil.frontend

import collection._
import org.rogach.scallop.LazyScallopConf
import semper.sil.verifier.Verifier
import org.rogach.scallop.exceptions.{ScallopException, Exit}

/**
 * The configuration of a SIL front-end.
 *
 * @author Stefan Heule
 */
case class SilFrontEndConfig(ars: Seq[String], verifier: Verifier) extends LazyScallopConf(ars) {
  var error: Option[String] = None
  val file = trailArg[String]("file", "The file to verify.", (x: String) => {
    val f = new java.io.File(x)
    f.canRead
  })

  version(s"${verifier.name} ${verifier.version} ${verifier.copyright}")
  banner( s"""Usage: ${verifier.name} [options] <file>
             |
             |Options:""".stripMargin)
  initialize {
    case Exit() =>
    case ScallopException(message) =>
      error = Some(message)
  }
}
