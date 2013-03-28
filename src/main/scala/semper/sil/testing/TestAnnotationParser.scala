package semper.sil.testing

/**
 * A parser for test annotations.  For an explanation of possible annotations and their syntax see
 * [[https://bitbucket.org/semperproject/sil/wiki/End-to-End%20Testing%20of%20Verifiers%20Based%20on%20SIL the description on the wiki]].
 *
 * @author Stefan Heule
 */
trait TestAnnotationParser {

  /** Takes a file as input and parses all test annotations present in that file and
    * returns an object describing the result.
    */
  def parseAnnotations(file: String): TestAnnotations = {
    val lines = file.replace("\r", "").split("\n").iterator.buffered
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
      if (l.startsWith("//::")) {
        if (l.startsWith("//:: ")) {
          l = l.substring(5)

          // what kind of annotation is it?
          isExpectedError(l, curLineNr,
            () => isUnexpectedError(l, curLineNr,
              () => isMissingError(l, curLineNr,
                () => isIgnoreFile(l, curLineNr)))) match {
            case Some(e) =>
              curAnnotations ::= e
            case None =>
              // could not parse it
              parseErrors ::= TestAnnotationParseError(l, curLineNr)
          }

          parsingAnnotations = true
        } else {
          // there should be a space -> report error
          parseErrors ::= TestAnnotationParseError(l, curLineNr)
        }
      } else if (l.startsWith("//")) {
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
    TestAnnotations(parseErrors.reverse, finalAnnotations.reverse)
  }

  /** At the time we parse a test annotation, we cannot know the `forLineNr` yet, so add it correctly now. */
  private def finishAnnotations(annotations: List[TestAnnotation], forLineNr: Int): List[TestAnnotation] = {
    for (a <- annotations) yield {
      a match {
        case ExpectedError(id, _, lineNr) => ExpectedError(id, forLineNr, lineNr)
        case UnexpectedError(id, _, lineNr, project, issueNr) => UnexpectedError(id, forLineNr, lineNr, project, issueNr)
        case MissingError(id, _, lineNr, project, issueNr) => MissingError(id, forLineNr, lineNr, project, issueNr)
        case _ => a
      }
    }
  }

  /** Try to parse the annotation as `ExpectedError`, and otherwise use `next`. */
  private def isExpectedError(annotation: String, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = """^ExpectedError\((.*)\)$""".r
    annotation match {
      case regex(id) => Some(ExpectedError(id, -1, lineNr))
      case _ => next()
    }
  }

  /** Try to parse the annotation as `UnexpectedError`, and otherwise use `next`. */
  private def isUnexpectedError(annotation: String, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = """^UnexpectedError\((.*), /(.*)/issue/([0-9]+)/\)$""".r
    annotation match {
      case regex(id, project, issueNr) => Some(UnexpectedError(id, -1, lineNr, project, issueNr.toInt))
      case _ => next()
    }
  }

  /** Try to parse the annotation as `MissingError`, and otherwise use `next`. */
  private def isMissingError(annotation: String, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = """^MissingError\((.*), /(.*)/issue/([0-9]+)/\)$""".r
    annotation match {
      case regex(id, project, issueNr) => Some(MissingError(id, -1, lineNr, project, issueNr.toInt))
      case _ => next()
    }
  }

  /** Try to parse the annotation a ``IgnoreFile``, and otherwise use `next`. */
  private def isIgnoreFile(annotation: String, lineNr: Int, next: () => Option[TestAnnotation] = () => None): Option[TestAnnotation] = {
    val regex = """^IgnoreFile\(/(.*)/issue/([0-9]+)/\)$""".r
    annotation match {
      case regex(project, issueNr) => Some(IgnoreFile(lineNr, project, issueNr.toInt))
      case _ => next()
    }
  }
}
