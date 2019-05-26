package viper.silver.plugin

import viper.silver.reporter._
import viper.silver.verifier.{Success, VerificationResult}

case class PluginAwareReporter(reporter: Reporter) {

  var transform: Function[VerificationResult, VerificationResult] = identity

  def report(msg: viper.silver.reporter.Message): Unit = {
    val transformedMsg =
      msg match {
        case OverallFailureMessage(ver, time, res) =>
          VerificationResultMessage(ver, time, transform(res))
        case OverallSuccessMessage(ver, time) =>
          VerificationResultMessage(ver, time, transform(Success))
        case EntityFailureMessage(ver, ent, time, res) =>
          VerificationResultMessage(ver, ent, time, transform(res))
        case EntitySuccessMessage(ver, ent, time) =>
          VerificationResultMessage(ver, ent, time, transform(Success))
        case _ => msg
      }
    reporter report transformedMsg
  }
}