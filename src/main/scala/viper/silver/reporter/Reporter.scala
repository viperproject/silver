/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.reporter

trait Reporter {
  val name: String

  def report(msg: Message): Unit
}

object NoopReporter extends Reporter {
  val name: String = "NoopReporter"
  def report(msg: Message): Unit = ()
}

case class StdIOReporter(name: String = "stdout_reporter", timeInfo: Boolean = true) extends Reporter {
  
  var counter = 0
  def timeStr(t: Time): String = f"${t*0.001}%.3f"

  def report(msg: Message): Unit = {
    msg match {
      case OverallFailureMessage(v, t, ex) =>
        if (!timeInfo)
          println(s"The following errors were found:")
        else
          println(s"The following errors were found in ${timeStr(t)} seconds:")
        ex.errors.foreach(e => println(s"  ${e.toString}"))

      case OverallSuccessMessage(v, t) =>
        if (!timeInfo)
          println(s"$v finished.")
        else
          println( s"$v finished in ${timeStr(t)} seconds." )
        println( s"Verification successful." )

      case ExceptionReport(e) =>
        /** Theoretically, we may encounter an exceptional message that has
          * not yet been reported via AbortedExceptionally. */
        println( s"Verification aborted exceptionally: ${e.toString}" )
        Option(e.getCause) match {
          case Some(cause) => println( s"  Cause: ${cause.toString}" )
          case None =>
        }
        //println( s"  See log file for more details: ..." )

      case ExternalDependenciesReport(deps) =>
        val s: String = (deps map (dep => {
          s"  ${dep.name} ${dep.version}, located at ${dep.location}."
        })).mkString("\n")
        println( s"The following dependencies are used:\n$s" )

      case InvalidArgumentsReport(tool_sig, errors) =>
        errors.foreach(e => println(s"  ${e.readableMessage}"))
        println( s"Run with just --help for usage and options" )

      case CopyrightReport(text) =>
        println( text )

      case EntitySuccessMessage(_, _, _) =>    // FIXME Currently, we only print overall verification results to STDOUT.
      case EntityFailureMessage(_, _, _, _) => // FIXME Currently, we only print overall verification results to STDOUT.
      case ConfigurationConfirmation(_) =>     // TODO  use for progress reporting
        //println( s"Configuration confirmation: $text" )
      case InternalWarningMessage(_) =>        // TODO  use for progress reporting
        //println( s"Internal warning: $text" )
      case sm:SimpleMessage =>
        //println( sm.text )
      case _ =>
        //println( s"Cannot properly print message of unsupported type: $msg" )
    }
    counter = counter + 1
  }
}

