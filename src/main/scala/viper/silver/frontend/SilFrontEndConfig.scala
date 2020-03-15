// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.frontend

import collection._
import org.rogach.scallop.{ScallopConf, ScallopOption}
import org.rogach.scallop.exceptions.{Help, ScallopException, Version}

/**
 * The configuration of a Viper front-end.
 */
abstract class SilFrontendConfig(args: Seq[String], private var projectName: String) extends ScallopConf(args) {
  /* Attention: projectName must be an explicit field, otherwise it cannot be
   * used in an interpolated string!
   */

  /** None if there has no error occurred during command-line parsing, and an error message otherwise. */
  var error: Option[String] = None

  /** True if (after command-line parsing) we should exit. */
  private var _exit: Boolean = false
  private var _printHelp = false

  def exit: Boolean = _printHelp || parseOnly.toOption.getOrElse(_exit)

  val parseOnly = opt[Boolean]("parseOnly",
    descr = "Exit right after parsing the program",
    default = Some(false),
    noshort = true,
    hidden = true)

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
    descr = "The Viper methods that should be verified. :all means all methods.",
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

  val disableCaching = opt[Boolean]("disableCaching",
    descr = (  "Used for ViperServer. Cache verification errors to speed up the"
      + "verification process"),
    default = Some(false),
    noshort = true,
    hidden = true
  )

  val ideModeAdvanced = opt[Boolean]("ideModeAdvanced",
    descr = "Used for symbolic execution debugging in ViperIDE. Produce the symbolic execution " +
      "log report.",
    default = Some(false),
    noshort = true,
    hidden = true
  )

  val consolidateOnAssertTrue = opt[Boolean]("consolidateOnAssertTrue",
    descr = "Specifies whether assert(true) triggers a state consolidation",
    default  = Some(false),
    noshort = true,
    hidden = true
  )

  val writeLogFile = opt[Boolean]("writeLogFile",
    descr = "Report the symbolic execution log as ExecutionTraceReport",
    default = Some(false),
    noshort = true,
    hidden = true
  )

  val plugin = opt[String]("plugin",
    descr = "Load plugin(s) with given class name(s). Several plugins can be separated by ':'. " +
      "The fully qualified class name of the plugin should be specified.",
    default = None,
    noshort = true,
    hidden = false
  )

  val terminationPlugin = opt[Boolean]("disableTerminationPlugin",
    descr = "Disable the termination plugin, which adds termination checks to functions, " +
      "methods and loops.",
    default = Some(false),
    noshort = true,
    hidden = true
  )

  validateOpt(file, ignoreFile) {
    case (_, Some(true)) => Right(Unit)
    case (Some(filepath), _) => validateFileOpt(file.name, filepath)
    case (optFile, optIgnoreFile) =>
      /* Since the file is a trailing argument and thus mandatory, this case
       * (in which optFile == None) should never occur.
       */
      sys.error(s"Unexpected combination of options ${file.name} ($optFile) and ${ignoreFile.name} ($optIgnoreFile)")
  }

  /* Validation helpers */

  protected def validateFileOpt(optionName: String, filepath: String): Either[String, Unit] = {
    val file = new java.io.File(filepath)
    if (!file.isFile) Left(s"Cannot find file '$filepath' from '$optionName' argument")
    else if (!file.canRead) Left(s"Cannot read from file '$filepath' from '$optionName' argument'")
    else Right(Unit)
  }

  protected def validateFileOpt(option: ScallopOption[String]): Unit = {
    validateOpt(option) {
      case None => Right(Unit)
      case Some(filepath) => validateFileOpt(option.name, filepath)
    }
  }

  /* Error handling */

  override def onError(e: Throwable): Unit = {
    _exit = true

    e match {
      case Version => println(builder.vers.get)
      case Help(_) =>
        _printHelp = true
        printHelp()
      case ScallopException(message) => error = Some(message)
      case unhandled => throw unhandled
    }
  }

  banner(s"""Usage: $projectName [options] <file>
            |
            |Options:""".stripMargin)
}
