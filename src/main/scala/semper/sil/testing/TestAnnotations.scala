package semper.sil.testing

import java.io.File
import semper.sil.verifier.AbstractError
import java.nio.file.Path

/**
 * The result of parsing the test annotations in a single file.
 *
 * @param errors The errors encountered during parsing.
 * @param annotations The test annotations found.
 *
 * @author Stefan Heule
 */
sealed case class TestAnnotations(errors: Seq[TestAnnotationParseError], annotations: Seq[TestAnnotation]) {
  def isFileIgnored(file: Path): Boolean = annotations exists {
    case _: IgnoreFileList => true
    case IgnoreFile(f, _, _, _) => f.toAbsolutePath == file.toAbsolutePath
    case _ => false
  }

  def hasErrors: Boolean = errors.size > 0

  /** Returns all the annotations without IgnoreFile and IgnoreFileList. */
  def errorAnnotations: Seq[LocatedAnnotation] = {
    annotations collect {
      case x: LocatedAnnotation => x
    }
  }
}

/** A trait for test annotations. */
sealed trait TestAnnotation

case class ErrorAnnotationId(reasonId: String, errorId: Option[String]) {
  override def toString = {
    errorId match {
      case None => reasonId
      case Some(i) => s"$i:$reasonId"
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

/** Annotations that refer to a location. */
sealed trait LocatedAnnotation extends TestAnnotation {
  val file: Path
  val forLineNr: Int
}

/** Test annotations that have a location and an identifier (i.e. describe an error of some sort). */
sealed abstract class ErrorAnnotation(val id: ErrorAnnotationId, val file: Path, val forLineNr: Int) extends LocatedAnnotation {
  override def toString = s"$id (${file.getFileName.toString}:$forLineNr)"
}

object ErrorAnnotation {
  def unapply(e: ErrorAnnotation) = Some((e.id, e.file, e.forLineNr))
}

sealed case class ExpectedError(override val id: ErrorAnnotationId, override val file: Path, override val forLineNr: Int, annotationLineNr: Int) extends ErrorAnnotation(id, file, forLineNr)

sealed case class UnexpectedError(override val id: ErrorAnnotationId, override val file: Path, override val forLineNr: Int, annotationLineNr: Int, project: String, issueNr: Int) extends ErrorAnnotation(id, file, forLineNr)

sealed case class MissingError(override val id: ErrorAnnotationId, override val file: Path, override val forLineNr: Int, annotationLineNr: Int, project: String, issueNr: Int) extends ErrorAnnotation(id, file, forLineNr)

sealed case class IgnoreOthers(file: Path, forLineNr: Int, annotationLineNr: Int) extends LocatedAnnotation

sealed case class IgnoreFile(file: Path, annotationLineNr: Int, project: String, issueNr: Int) extends TestAnnotation

sealed case class IgnoreFileList(file: Path, annotationLineNr: Int, project: String, issueNr: Int) extends TestAnnotation

case class TestAnnotationParseError(offendingLine: String, file: Path, lineNr: Int) {
  def errorMessage: String = {
    s"Line ${lineNr} in ${file.toString} looks like a test annotation (it starts with '//::'), but it was not " +
      s"possible to parse it correctly.  The line is : '$offendingLine'."
  }
}
