package semper.sil.testing

import java.nio.file.{Files, Path}

/**
 * The result of parsing the test annotations in a single file.
 *
 * @param errors The errors encountered during parsing.
 * @param annotations The test annotations found.
 *
 * @author Stefan Heule
 */
sealed case class TestAnnotations(errors: Seq[TestAnnotationParseError], annotations: Seq[TestAnnotation]) {
  def isFileIgnored(file: Path, project: String): Boolean = annotations exists {
    case _: IgnoreFileList => true
    case IgnoreFile(f, _, prj, _) => f.toAbsolutePath == file.toAbsolutePath && prj.equalsIgnoreCase(project)
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
  def file: Path
  def forLineNr: Int

  def sameSource(other: LocatedAnnotation) =
    Files.isSameFile(this.file, other.file) && forLineNr == other.forLineNr
}

/** Test annotations that have a location and an identifier (i.e. describe an error of some sort). */
sealed trait ErrorAnnotation extends LocatedAnnotation {
  def id: ErrorAnnotationId

  override def toString = s"$id (${file.getFileName.toString}:$forLineNr)"
}

/** Test annotation that is specific to a certain project. Further details should be given by the referenced issue. */
sealed trait ProjectSpecificAnnotation extends TestAnnotation {
  def project: String
  def issueNr: Int
}

object ErrorAnnotation {
  def unapply(e: ErrorAnnotation) = Some((e.id, e.file, e.forLineNr))
}

case class ExpectedError(id: ErrorAnnotationId, file: Path, forLineNr: Int, annotationLineNr: Int) extends ErrorAnnotation

case class UnexpectedError(id: ErrorAnnotationId, file: Path, forLineNr: Int, annotationLineNr: Int, project: String, issueNr: Int) extends ErrorAnnotation with ProjectSpecificAnnotation

case class MissingError(id: ErrorAnnotationId, file: Path, forLineNr: Int, annotationLineNr: Int, project: String, issueNr: Int) extends ErrorAnnotation with ProjectSpecificAnnotation

case class IgnoreOthers(file: Path, forLineNr: Int, annotationLineNr: Int) extends LocatedAnnotation

case class IgnoreFile(file: Path, annotationLineNr: Int, project: String, issueNr: Int) extends ProjectSpecificAnnotation

case class IgnoreFileList(file: Path, annotationLineNr: Int, project: String, issueNr: Int) extends ProjectSpecificAnnotation

case class TestAnnotationParseError(offendingLine: String, file: Path, lineNr: Int) {
  def errorMessage: String = {
    s"Line ${lineNr} in ${file.toString} looks like a test annotation (it starts with '//::'), but it was not " +
      s"possible to parse it correctly.  The line is : '$offendingLine'."
  }
}
