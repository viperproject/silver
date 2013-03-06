package semper.sil.frontend

import collection._
import org.rogach.scallop.LazyScallopConf
import semper.sil.verifier.Verifier
import org.rogach.scallop.exceptions.{Help, Version, ScallopException, Exit}

/**
 * The configuration of a SIL front-end.
 *
 * @author Stefan Heule
 */
case class SilFrontendConfig(ars: Seq[String], verifier: Verifier) extends LazyScallopConf(ars) {

  /** None if there has no error occurred during command-line parsing, and an error message oderwise. */
  var error: Option[String] = None
  /** True if (after command-line parsing) we should exit. */
  var exit: Boolean = false

  val file = trailArg[String]("file", "The file to verify.", (x: String) => {
    val f = new java.io.File(x)
    f.canRead
  }, hidden = true)

  val noTiming = opt[Boolean]("no-timing",
    descr = "Don't display timing information",
    default = Some(false),
    noshort = true
  )

  val noHeader = opt[Boolean]("no-header",
    descr = "Don't display the header (includes name and version of the tool as well as its dependencies)",
    default = Some(false),
    noshort = true
  )

  val detailedTiming = opt[Boolean]("detailed-timing",
    descr = "Display detailed timing information",
    default = Some(false),
    noshort = true
  )

  def fullVersion = {
    val depToString = ((dep: (String, String)) => s"${dep._1} ${dep._2}")
    val dep = verifier.dependencyVersions match {
      case Nil => ""
      case deps => "\n  using " + (deps map depToString).mkString(", ") + " "
    }
    s"${verifier.name} ${verifier.version} ${verifier.copyright}$dep"
  }

  version(fullVersion)
  banner( s"""Usage: ${verifier.name} [options] <file>
             |
             |Options:""".stripMargin)
  initialize {
    case Version =>
      println(builder.vers.get)
      exit = true
    case Help(_) =>
      exit = true
      printHelp()
    case ScallopException(message) =>
      error = Some(message)
  }
}
