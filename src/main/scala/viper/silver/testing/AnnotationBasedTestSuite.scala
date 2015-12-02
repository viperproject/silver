/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.testing

import java.nio.file.Path
import org.scalatest.Tag

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
      val outputErrors = OutputMatcher(actualOutputs, expectedOutputs).errors

      // All errors
      val errors = parserErrors ++ outputErrors

      // If there were any outputs that could not be matched up
      // (or other problems), make the test fail
      if (errors.nonEmpty) {
        val title = s"${errors.size} errors"
        val body = errors.groupBy(_.errorType).map({
          case (typ, es) =>
            TestErrorType.message(typ) + ":\n" + es.map("  " + _.message).mkString("\n")
        }).mkString("\n\n")
        fail(title + "\n\n" + body + "\n\n")
      }
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
        case l => l.find(_.isInstanceOf[OutputAnnotation]) match {
          case Some(x) =>
            // Remove the output from the list of expected output
            // (i.e. only match once)
            remainingOutputs = remainingOutputs.filterNot(_.eq(x))
            Some(x)
          case None =>
            Some(l.head) // IgnoreOthers should not be removed
        }
      }
    }

    // Separate missing outputs from remaining outputs
    val missingOutputs = remainingOutputs.collect{case m: MissingOutput => m}
    remainingOutputs = remainingOutputs.filterNot(missingOutputs.contains)

    // Process remaining outputs that have not been matched
    remainingOutputs.foreach {
      case e: ExpectedOutput =>
        if (!missingOutputs.exists(_.sameSource(e)))
          errors ::= TestExpectedButMissingOutputError(e)
      case u: UnexpectedOutput =>
        errors ::= TestUnexpectedButMissingOutputError(u)
      case _: IgnoreOthers =>
      case _: MissingOutput =>
        sys.error("Should not occur because they were previously filtered")
    }

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
 * such that the testing infrastructure is independent from SIL's AST.
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
