// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.testing

import java.nio.file.{Files, Path}
import scala.io.Source

/**
 * A parser for test annotations.  For an explanation of possible annotations and their syntax see
 * [[https://bitbucket.org/viperproject/silver/wiki/End-to-End%20Testing%20of%20Verifiers%20Based%20on%20SIL the description on the wiki]].
 */
trait TestAnnotationParser {

  /**
   * Sequence that starts a comment in the language that is parsed. Can be overridden if a language is used that
   * has something else than `//` as the start of a single line comment.
   */
  val commentStart = "//"

  /**
   * Takes a sequence of files as input and parses all test annotations present in those
   * files and returns an object describing the result.
   */
  def parseAnnotations(files: Seq[Path]): TestAnnotations = {
    val (parseErrors, annotations) = (files map parseAnnotations).unzip
    TestAnnotations(parseErrors.flatten, annotations.flatten)
  }

  /** Takes a file as input and parses all test annotations present in that file and
    * returns an object describing the result.
    */
  def parseAnnotations(file: Path) = {
    val lines = Source.fromInputStream(Files.newInputStream(file))
                      .mkString
                      .replace("""\r""", "")
                      .split("\n")
                      .iterator
                      .buffered
    var curLineNr = 0
    var curAnnotations: List[TestAnnotation] = Nil
    var finalAnnotations: List[TestAnnotation] = Nil
    var parseErrors: List[TestAnnotationParseError] = Nil
    // indicates that the last line we saw was a test annotation, and that we are currently looking for more test
    // annotations on the coming lines (recall that the target line for a test annotation is the next line that
    // is not a comment or another test annotation
    var parsingAnnotations = false

    // go through all lines to find test annotations
    while (lines.hasNext) {
      var l = lines.next().trim
      curLineNr += 1

      // found a line that looks like a test annotations
      if (l.startsWith(commentStart + "::")) {
        if (l.startsWith(commentStart + ":: ")) {
          l = l.substring(5)

          // what kind of annotation is it?
          isExpectedOutput(l, file, curLineNr,
            () => isUnexpectedOutput(l, file, curLineNr,
              () => isMissingOutput(l, file, curLineNr,
                () => isIgnoreOthers(l, file, curLineNr,
                  () => isIgnoreFile(l, file, curLineNr,
                    () => isIgnoreFileList(l, file, curLineNr)))))) match {
            case Some(e) =>
              curAnnotations ::= e
            case None =>
              // could not parse it
              parseErrors ::= TestAnnotationParseError(l, file, curLineNr)
          }

          parsingAnnotations = true
        } else {
          // there should be a space -> report error
          parseErrors ::= TestAnnotationParseError(l, file, curLineNr)
        }
      } else if (l.startsWith(commentStart)) {
        // ignore comments
      } else {
        // finish parsing annotations
        if (parsingAnnotations) {
          finalAnnotations :::= finishAnnotations(curAnnotations, curLineNr)
          curAnnotations = Nil
          parsingAnnotations = false
        }
      }
    }
    (parseErrors.reverse, finalAnnotations.reverse)
  }

  /** At the time we parse a test annotation, we cannot know the `forLineNr` yet, so add it correctly now. */
  private def finishAnnotations(annotations: List[TestAnnotation], forLineNr: Int): List[TestAnnotation] = {
    for (a <- annotations) yield {
      a match {
        case ExpectedOutput(id, file, _, lineNr) => ExpectedOutput(id, file, forLineNr, lineNr)
        case UnexpectedOutput(id, file, _, lineNr, project, issueNr) => UnexpectedOutput(id, file, forLineNr, lineNr, project, issueNr)
        case MissingOutput(id, file, _, lineNr, project, issueNr) => MissingOutput(id, file, forLineNr, lineNr, project, issueNr)
        case IgnoreOthers(file, _, lineNr) => IgnoreOthers(file, forLineNr, lineNr)
        case _ => a
      }
    }
  }

  /**
   * A regular expression that matches an output id,
   * either only using the output reason, or with the full id.
   */
  val outputIdPattern = "([^:]*)(:(.*))?"

  /** Try to parse the annotation as `ExpectedOutput`, and otherwise use `next`. */
  private def isExpectedOutput(annotation: String, file: Path, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = ("""^ExpectedOutput\(""" + outputIdPattern + """\)$""").r
    annotation match {
      case regex(keyId, _, null) =>
        Some(ExpectedOutput(OutputAnnotationId(keyId, None), file, -1, lineNr))
      case regex(keyId, _, valueId) =>
        Some(ExpectedOutput(OutputAnnotationId(keyId, Some(valueId)), file, -1, lineNr))
      case _ => next()
    }
  }

  /** Try to parse the annotation as `UnexpectedOutput`, and otherwise use `next`. */
  private def isUnexpectedOutput(annotation: String, file: Path, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = ("""^UnexpectedOutput\(""" + outputIdPattern + """, /(.*)/issue/([0-9]+)/\)$""").r
    annotation match {
      case regex(reasonId, _, null, project, issueNr) =>
        Some(UnexpectedOutput(OutputAnnotationId(reasonId, None), file, -1, lineNr, project, issueNr.toInt))
      case regex(keyId, _, valueId, project, issueNr) =>
        Some(UnexpectedOutput(OutputAnnotationId(keyId, Some(valueId)), file, -1, lineNr, project, issueNr.toInt))
      case _ => next()
    }
  }

  /** Try to parse the annotation as `MissingOutput`, and otherwise use `next`. */
  private def isMissingOutput(annotation: String, file: Path, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = ("""^MissingOutput\(""" + outputIdPattern + """, /(.*)/issue/([0-9]+)/\)$""").r
    annotation match {
      case regex(reasonId, _, null, project, issueNr) =>
        Some(MissingOutput(OutputAnnotationId(reasonId, None), file, -1, lineNr, project, issueNr.toInt))
      case regex(keyId, _, valueId, project, issueNr) =>
        Some(MissingOutput(OutputAnnotationId(keyId, Some(valueId)), file, -1, lineNr, project, issueNr.toInt))
      case _ => next()
    }
  }

   /** Try to parse the annotation a ``IgnoreOthers``, and otherwise use `next`. */
  private def isIgnoreOthers(annotation: String, file: Path, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = """^IgnoreOthers$""".r
    annotation match {
      case regex() => Some(IgnoreOthers(file, -1, lineNr))
      case _ => next()
    }
  }

  /** Try to parse the annotation a ``IgnoreFile``, and otherwise use `next`. */
    private def isIgnoreFile(annotation: String, file: Path, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = """^IgnoreFile\(/(.*)/issue/([0-9]+)/\)$""".r
    annotation match {
      case regex(project, issueNr) => Some(IgnoreFile(file, lineNr, project, issueNr.toInt))
      case _ => next()
    }
  }

   /** Try to parse the annotation a ``IgnoreFileList``, and otherwise use `next`. */
  private def isIgnoreFileList(annotation: String, file: Path, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = """^IgnoreFileList\(/(.*)/issue/([0-9]+)/\)$""".r
    annotation match {
      case regex(project, issueNr) => Some(IgnoreFileList(file, lineNr, project, issueNr.toInt))
      case _ => next()
    }
  }

}
