package viper.silver.plugin

import viper.silver.reporter._
import viper.silver.verifier.{Success, VerificationResult}


// TODO consider implementing caching for verification results that were already mapped before.
case class PluginAwareReporter(reporter: Reporter) {

  var transform: Function[VerificationResult, VerificationResult] = identity

  def report(msg: viper.silver.reporter.Message): Unit = {
    val transformedMsg =
      msg match {
        case OverallFailureMessage(ver, time, res) =>
//          println(s"--- PluginAwareReporter::report   transform($res) = ${transform(res)}")
          VerificationResultMessage(ver, time, transform(res))
        case OverallSuccessMessage(ver, time) =>
//          println(s"--- PluginAwareReporter::report   transform(Success) = ${transform(Success)}")
          VerificationResultMessage(ver, time, transform(Success))
        case EntityFailureMessage(ver, ent, time, res) =>
//          println(s"--- PluginAwareReporter::report   transform($res) = ${transform(res)}")
          VerificationResultMessage(ver, ent, time, transform(res))
        case EntitySuccessMessage(ver, ent, time) =>
//          println(s"--- PluginAwareReporter::report   transform(Success) = ${transform(Success)}")
          VerificationResultMessage(ver, ent, time, transform(Success))
        case _ => msg
      }
    reporter report transformedMsg
  }
}