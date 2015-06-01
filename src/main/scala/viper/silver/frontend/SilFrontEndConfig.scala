/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.frontend

import collection._
import org.rogach.scallop.LazyScallopConf

/**
 * The configuration of a SIL front-end.
 */
class SilFrontendConfig(args: Seq[String], private var projectName: String) extends LazyScallopConf(args) {
  /* Attention: projectName must be an explicit field, otherwise it cannot be
    * used in an interpolated string!
    */

  /** None if there has no error occurred during command-line parsing, and an error message otherwise. */
  var error: Option[String] = None

  /** True if (after command-line parsing) we should exit. */
  var exit: Boolean = false

  /** Should be true after `LazyScallopConf.initialize` has been called,
    * i.e., it should be set to true by the closure passed to `LazyScallopConf.initialize`.
    */
  var initialized: Boolean = false

  val file = trailArg[String]("file", "The file to verify.")/*, (x: String) => {
    val f = new java.io.File(x)
    f.canRead
  })*/

  val dependencies = opt[Boolean]("dependencies",
    descr = "Print full information about dependencies.",
    default = Some(false),
    noshort = true,
    hidden = true
  )

  val noTiming = opt[Boolean]("no-timing",
    descr = "Don't display timing information",
    default = Some(false),
    noshort = true,
    hidden = true
  )

  val methods = opt[String]("methods",
    descr = "The SIL methods that should be verified. :all means all methods.",
    default = Some(":all"),
    noshort = true,
    hidden = true
  )

  val ignoreFile = opt[Boolean]("ignoreFile",
    descr = "Ignore the file (in particular, don't check that it can actually be read).",
    default = Some(false),
    noshort = true,
    hidden = true
  )

  val ideMode = opt[Boolean]("ideMode",
    descr = (  "Report errors in the format '<file>,<line>:<col>: <message>', and write"
             + "errors in the format '<file>,<line>:<col>,<line>:<col>,<message>' to"
             + "a file (see option ideModeErrorFile)."),
    default = Some(false),
    noshort = true,
    hidden = true
  )

  val ideModeErrorFile = opt[String]("ideModeErrorFile",
    descr = "File to which errors should be written",
    default = Some("errors.log"),
    noshort = true,
    hidden = true
  )

  dependsOnAll(ideModeErrorFile, ideMode :: Nil)

  validateOpt(file, ignoreFile) {
    case (_, Some(true)) => Right(Unit)
    case (Some(path), _) =>
      if (new java.io.File(path).canRead) Right(Unit)
      else Left(s"Cannot read $path")
    case (optFile, optIgnoreFile) =>
      /* Since the file is a trailing argument and thus mandatory, this case
       * (in which optFile == None) should never occur.
       */
      sys.error(s"Unexpected combination of $optFile and $optIgnoreFile")
  }

  banner(s"""Usage: $projectName [options] <file>
            |
            |Options:""".stripMargin)
}
