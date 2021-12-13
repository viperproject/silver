// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.testing

import java.nio.file.Path

/**
 * The types of errors that can be revealed by
 * [[viper.silver.testing.AnnotationBasedTestSuite]].
 *
 * This enumeration makes it easy to group errors by type and to
 * store data that is not specific to an individual error, but an error type.
 */
object TestErrorType extends Enumeration {
  type TestErrorType = Value

  val AnnotationParsing = Value
  val AdditionalOutput = Value
  val ExpectedButMissingOutput = Value
  val UnexpectedButMissingOutput = Value
  val MissingButPresentOutputs = Value

  /** The message to be displayed before all errors of the same given type. */
  def message(error: TestErrorType): String = error match {
    case AnnotationParsing =>
      "Encountered the following errors while parsing " +
        "the test annotations (these annotations will be ignored)"
    case AdditionalOutput =>
      "The following output occurred during testing, " +
        "but should not have according to the test annotations"
    case ExpectedButMissingOutput =>
      "The following outputs were expected according to the test " +
        "annotations, but did not occur during testing"
    case UnexpectedButMissingOutput =>
      "The following outputs was specified to occur erroneously " +
        "(UnexpectedOutput) according to the test annotations, " +
        "but did not occur during testing"
    case MissingButPresentOutputs =>
      "The following outputs were specified to be missing erroneously " +
        "(MissingOutput) according to the test annotations, but did occur " +
        "during testing (this might be cause by invalid test annotations)"
  }
}

/**
 * An error revealed by the test suite.
 *
 * It would be possible to create separate case classes for each type of error,
 * but for the moment, the error type and an error message is enough.
 */
abstract class TestError(val errorType: TestErrorType.Value) {
  def message: String
}

case class TestAnnotationParseError(
    offendingLine: String,
    file: Path,
    lineNr: Int) extends TestError(TestErrorType.AnnotationParsing) {
  def message =
    s"Line $lineNr in ${file.toString} looks like a test annotation " +
      s"(it starts with '//::'), but it was not possible to parse it correctly. " +
      s"The line is '$offendingLine'."
}

case class TestAdditionalOutputError(output: AbstractOutput)
    extends TestError(TestErrorType.AdditionalOutput) {

  def message = "[" +output.fullId + "] " + output.toString
}

case class TestExpectedButMissingOutputError(expectedOutput: ExpectedOutput)
    extends TestError(TestErrorType.ExpectedButMissingOutput) {

  def message = expectedOutput.toString
}

case class TestUnexpectedButMissingOutputError(unexpectedOutput: UnexpectedOutput)
    extends TestError(TestErrorType.UnexpectedButMissingOutput) {

  def message = unexpectedOutput.toString
}

case class TestMissingButPresentOutputError(missingOutput: MissingOutput, output: AbstractOutput)
    extends TestError(TestErrorType.MissingButPresentOutputs) {

  def message = output.toString
}
