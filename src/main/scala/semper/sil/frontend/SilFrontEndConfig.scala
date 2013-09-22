package semper.sil.frontend

import collection._
import org.rogach.scallop.LazyScallopConf
import semper.sil.verifier.{Verifier}
import org.rogach.scallop.exceptions.{Help, Version, ScallopException}

/**
 * The configuration of a SIL front-end.
 *
 * @author Stefan Heule
 */
class SilFrontendConfig(args: Seq[String], private var projectName: String) extends LazyScallopConf(args) {
  /* Attention: projectName must be an explicit field, otherwise it cannot be
    * used in an interpolated string!
    */

  /** None if there has no error occurred during command-line parsing, and an error message otherwise. */
  var error: Option[String] = None

  /** True if (after command-line parsing) we should exit. */
  var exit: Boolean = false

  val file = trailArg[String]("file", "The file to verify.", (x: String) => {
    val f = new java.io.File(x)
    f.canRead
  })

  val dependencies = opt[Boolean]("dependencies",
    descr = "Print full information about dependencies.",
    default = Some(false),
    noshort = true
  )

  val noTiming = opt[Boolean]("no-timing",
    descr = "Don't display timing information",
    default = Some(false),
    noshort = true
  )

  val methods = opt[String]("methods",
    descr = "The SIL methods that should be verified. :all means all methods.",
    default = Some(":all"),
    noshort = true
  )

  banner(s"""Usage: $projectName [options] <file>
            |
            |Options:""".stripMargin)
}
