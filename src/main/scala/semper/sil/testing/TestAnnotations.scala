package semper.sil.testing

/**
 * The result of parsing the test annotations in a single file.
 *
 * @param errors The errors encountered during parsing.
 * @param annotations The test annotations found.
 *
 * @author Stefan Heule
 */
sealed case class TestAnnotations(errors: Seq[TestAnnotationParseError], annotations: Seq[TestAnnotation]) {
  def isFileIgnored: Boolean = annotations contains ((x: TestAnnotation) => x match {
    case _: IgnoreFile => true
    case _ => false
  })

  def hasErrors: Boolean = errors.size > 0

  /** Returns all the annotations without 'ignores'. */
  def errorAnnotations: Seq[ErrorAnnotation] = {
    annotations flatMap {
      case x: ExpectedError => x :: Nil
      case x: UnexpectedError => x :: Nil
      case x: MissingError => x :: Nil
      case _ => Nil
    }
  }
}

/** A trait for test annotations. */
trait TestAnnotation

/** Test annotations that have a location and an identifier (i.e. describe an error of some sort). */
abstract class ErrorAnnotation(val id: String, val forLineNr: Int) extends TestAnnotation

object ErrorAnnotation {
  def unapply(e: ErrorAnnotation) = Some((e.id, e.forLineNr))
}

sealed case class ExpectedError(override val id: String, override val forLineNr: Int, annotationLineNr: Int) extends ErrorAnnotation(id, forLineNr)

sealed case class UnexpectedError(override val id: String, override val forLineNr: Int, annotationLineNr: Int, project: String, issueNr: Int) extends ErrorAnnotation(id, forLineNr)

sealed case class MissingError(override val id: String, override val forLineNr: Int, annotationLineNr: Int, project: String, issueNr: Int) extends ErrorAnnotation(id, forLineNr)

sealed case class IgnoreFile(annotationLineNr: Int, project: String, issueNr: Int) extends TestAnnotation

case class TestAnnotationParseError(offendingLine: String, lineNr: Int) {
  def errorMessage: String = {
    s"Line ${lineNr} looks like a test annotation (it starts with '//::'), but it was not " +
      s"possible to parse it correctly.  The line is : '$offendingLine'."
  }
}
