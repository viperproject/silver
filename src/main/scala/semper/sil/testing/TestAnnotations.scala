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
sealed trait TestAnnotation

case class ErrorAnnotationId(reasonId: String, errorId: Option[String]) {
  override def toString = {
    errorId match {
      case None => reasonId
      case Some(i) => s"$i.$reasonId"
    }
  }

  def matches(id: String): Boolean = {
    val ids = id.split(":")
    if (ids.size == 1) {
      return errorId == None && reasonId == id
    }
    assert(ids.size == 2, s"Expected full ID, but got $id.")
    errorId match {
      case None => reasonId == ids(1)
      case Some(s) => s == ids(0) && reasonId == ids(1)
    }
  }
}

/** Test annotations that have a location and an identifier (i.e. describe an error of some sort). */
sealed abstract class ErrorAnnotation(val id: ErrorAnnotationId, val forLineNr: Int) extends TestAnnotation {
  override def toString = s"$forLineNr.*: $id"
}

object ErrorAnnotation {
  def unapply(e: ErrorAnnotation) = Some((e.id, e.forLineNr))
}

sealed case class ExpectedError(override val id: ErrorAnnotationId, override val forLineNr: Int, annotationLineNr: Int) extends ErrorAnnotation(id, forLineNr)

sealed case class UnexpectedError(override val id: ErrorAnnotationId, override val forLineNr: Int, annotationLineNr: Int, project: String, issueNr: Int) extends ErrorAnnotation(id, forLineNr)

sealed case class MissingError(override val id: ErrorAnnotationId, override val forLineNr: Int, annotationLineNr: Int, project: String, issueNr: Int) extends ErrorAnnotation(id, forLineNr)

sealed case class IgnoreFile(annotationLineNr: Int, project: String, issueNr: Int) extends TestAnnotation

case class TestAnnotationParseError(offendingLine: String, lineNr: Int) {
  def errorMessage: String = {
    s"Line ${lineNr} looks like a test annotation (it starts with '//::'), but it was not " +
      s"possible to parse it correctly.  The line is : '$offendingLine'."
  }
}
