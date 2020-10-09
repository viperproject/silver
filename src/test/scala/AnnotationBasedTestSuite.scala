// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.testing

import org.scalatest.Tag
import java.nio.file.Path

/**
 * End-to-end test suite that extracts [[viper.silver.testing.TestAnnotations]]
 * from input files and asserts that the output of the system under test
 * agrees with the annotations.
 *
 * It's possible to test multiple systems (e.g. verifiers) at once.
 * The test suite will run each test on each system.
 */
abstract class AnnotationBasedTestSuite extends ResourceBasedTestSuite {
  override type InputType = AnnotatedTestInput

  /**
   * The systems to test each input on.
   *
   * This method is not modeled as a constant field deliberately, such that
   * subclasses can instantiate a new [[viper.silver.testing.SystemUnderTest]]
   * for each test input.
   */
  def systemsUnderTest: Seq[SystemUnderTest]

  def buildTestInput(file: Path, prefix: String) =
    DefaultAnnotatedTestInput(file, prefix)

  /** Registers a given test input for a given system under test. */
  def registerTest(input: AnnotatedTestInput, system: SystemUnderTest) = {
//    info(input.name)

    test(input.name, input.tags :_*) {
      // Error for parse failures of test annotations
      val parserErrors = input.annotations.errors

      // Match expected outputs with actual outputs
      val actualOutputs = system.run(input)
      val expectedOutputs = input.annotations.outputAnnotations

      val matcher = OutputMatcher(actualOutputs, expectedOutputs)
      val unexpectedAnnotations = input.annotations.outputAnnotations.filter(annotationShouldLeadToTestCancel)
      val outputErrors = matcher.errors

      // All errors
      val (errors, ignoredErrors) = (parserErrors ++ outputErrors).partition(!errorShouldLeadToTestCancel(_))

      // If there were any outputs that could not be matched up
      // (or other problems), make the test fail,
      // except if there are errors that make the test ignored
      if (errors.nonEmpty && ignoredErrors.isEmpty) {
        val title = s"${errors.size} errors"
        val body = errors.groupBy(_.errorType).map({
          case (typ, es) =>
            TestErrorType.message(typ) + ":\n" + es.map("  " + _.message).mkString("\n")
        }).mkString("\n\n")
        fail(title + "\n\n" + body + "\n\n")
      }
      // If the test succeeds, but there were annotations for unexpected
      // or missing outputs, we mark the test as cancelled.
      // If the test fails with some specific error type, we also mark it as cancelled.
      if (unexpectedAnnotations.nonEmpty || ignoredErrors.nonEmpty) {
        val title = s"${unexpectedAnnotations.size + ignoredErrors.size} ignored errors"
        val body = (unexpectedAnnotations.map({
          case UnexpectedOutput(id, _, _, _, _, issue) =>
            id.toString + ", issue " + issue
          case MissingOutput(id, _, _, _, _, issue) =>
            id.toString + ", issue " + issue
          case _ => ""
        })
          ++ ignoredErrors.groupBy(_.errorType).map({
          case (typ, es) =>
            TestErrorType.message(typ) + ":\n" + es.map("  " + _.message).mkString("\n")
        })).mkString("\n")
        cancel(title + "\n" + body + "\n")
      }
    }
  }

  def errorShouldLeadToTestCancel(err: TestError) = false

  def annotationShouldLeadToTestCancel(ann: LocatedAnnotation) = {
    ann match {
      case UnexpectedOutput(_, _, _, _, _, _) => true
      case MissingOutput(_, _, _, _, _, _) => true
      case _ => false
    }
  }

  def registerTest(input: AnnotatedTestInput) = {
    require(input != null)

    for (system <- systemsUnderTest) {
      // Builds a new test input for the specific system under test.
      // For example, it may ignore files if necessary.
      val newInput = input.makeForProject(system.projectInfo)
      if (newInput.files.isEmpty)
        ignore(newInput.name, newInput.tags: _*) {}
      else
        registerTest(newInput, system)
    }
  }
}

/**
 * Finds the inconsistencies between the expected output and the actual
 * output of the system under test and builds the corresponding errors.
 *
 * It assumes that all annotations are relevant. That is, filter the
 * annotations first to exclude annotations specific to other projects
 * before giving them to the matcher.
 *
 * @param actualOutputs the output produced by the system under test
 * @param expectedOutputs the output expected according to the annotations
 */
case class OutputMatcher(
    actualOutputs: Seq[AbstractOutput],
    expectedOutputs: Seq[LocatedAnnotation]) {

  lazy val errors: Seq[TestError] = {
    var errors = List[TestError]()
    var remainingOutputs = expectedOutputs

    // Go through all actual outputs and try to match them up
    // with the expected ones
    actualOutputs foreach (a => findOutput(a) match {
      case Some(m: MissingOutput) => errors ::= TestMissingButPresentOutputError(m, a)
      case Some(_) => // expected this error
      case None => errors ::= TestAdditionalOutputError(a)
    })

    def findOutput(actual: AbstractOutput): Option[TestAnnotation] = {
      expectedOutputs.filter({
        case OutputAnnotation(id, file, lineNr) =>
          id.matches(actual.fullId) && actual.isSameLine(file, lineNr)
        case IgnoreOthers(file, lineNr, _) =>
          actual.isSameLine(file, lineNr)
      }) match {
        case Nil => None
        case l => l.find(o => o.isInstanceOf[MissingOutput]) match // prioritise missing output annotations which match
        {
          case Some(mo) => Some(mo) // this is an error - declared missing, but it happened (the fact that this is a problem is handled in the calling code)
          case None => l.find(o => o.isInstanceOf[ExpectedOutput] || o.isInstanceOf[UnexpectedOutput]) match {
            case Some(eo) =>
              remainingOutputs = remainingOutputs.diff(Seq(eo)) // note: diff removes exactly one instance
              Some(eo) // this case is OK - we matched an annotation for this output
            case None => l.head match {
              case io@IgnoreOthers(_, _, _) => Some(io)
              case _ => sys.error("Unexpected error annotation type in test-annotation matching code")
            }
          }
        }
      }
    }

    // Separate missing outputs from remaining outputs
    var missingOutputs : Seq[MissingOutput] = remainingOutputs.collect{case m: MissingOutput => m}
    remainingOutputs = remainingOutputs.filterNot(missingOutputs.contains)

    // Process remaining outputs that have not been matched
    remainingOutputs.foreach { _ match {
      case e: ExpectedOutput =>
        missingOutputs.find(_.sameSource(e)) match {
          case Some(mo) => missingOutputs = missingOutputs.diff(Seq(e))
          case None => errors ::= TestExpectedButMissingOutputError(e)
        }
      case u: UnexpectedOutput =>
        errors ::= TestUnexpectedButMissingOutputError(u)
      case _: IgnoreOthers =>
      case _: MissingOutput =>
        sys.error("MissingOutput should not occur here because they were previously filtered")
    }
    }

    // Process remaining MissingOutput annotations which did not correspond to a missing output

    errors.toSeq
  }
}

/** The system that produces output given the test input. */
trait SystemUnderTest {
  /** For filtering test annotations. Does not need to be unique. */
  val projectInfo: ProjectInfo

  def run(input: AnnotatedTestInput): Seq[AbstractOutput]
}

/**
 * An output produced by a system under test.
 *
 * It deliberately does not reference [[viper.silver.ast.Position]],
 * such that the testing infrastructure is independent from Viper's AST.
 *
 * Its `toString` method will be used to output an error message
 * if the output was not supposed occur.
 */
trait AbstractOutput {
  /** Whether the output belongs to the given line in the given file. */
  def isSameLine(file: Path, lineNr: Int): Boolean

  /** A short and unique identifier for this output. */
  def fullId: String
}

/** Test input that also includes test annotations. */
trait AnnotatedTestInput extends TestInput {
  val annotations: TestAnnotations

  /** Create a test input that is specific to the given project. */
  def makeForProject(projectInfo: ProjectInfo): AnnotatedTestInput
}

/** Test input that also includes test annotations. */
case class DefaultAnnotatedTestInput(
    name: String,
    prefix: String,
    files: Seq[Path],
    tags: Seq[Tag],
    annotations: TestAnnotations) extends AnnotatedTestInput {
  /**
   * Create a test input that is specific to the given project.
   *
   * It creates an additional tag, filters files according to annotations
   * and also filters the annotations themselves.
   */
  def makeForProject(projectInfo: ProjectInfo): DefaultAnnotatedTestInput = {
    val ignore = (file: Path) => projectInfo.projectNames.exists(annotations.isFileIgnored(file, _))
    copy(
      name = s"$name [${projectInfo.fullName}]",
      files = files.filter(!ignore(_)),
      tags = projectInfo.projectNames.map(Tag(_)) ++ tags.toList,
      annotations = annotations.filterByProject(projectInfo))
  }
}

object DefaultAnnotatedTestInput extends TestAnnotationParser {
  /**
   * Creates an annotated test input by parsing all annotations in the files
   * that belong to the given test input.
   */
  def apply(i: TestInput): DefaultAnnotatedTestInput =
    DefaultAnnotatedTestInput(i.name, i.prefix, i.files, i.tags,
      parseAnnotations(i.files))

  def apply(file: Path, prefix: String): DefaultAnnotatedTestInput =
    apply(DefaultTestInput(file, prefix))
}
