package viper.silver.plugin

import viper.silver.reporter._
import viper.silver.verifier.{Failure, Success, VerificationResult}


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
        case efm:EntityFailureMessage =>
          efm.copy(result = transform(efm.result).asInstanceOf[Failure])
        //          println(s"--- PluginAwareReporter::report   transform($res) = ${transform(res)}")
        case esm: EntitySuccessMessage =>
          esm.copy(result = transform(Success))
        //          println(s"--- PluginAwareReporter::report   transform(Success) = ${transform(Success)}")
        case _ => msg
      }
    reporter report transformedMsg
  }
}

