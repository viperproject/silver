/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.sil.testing

import java.nio.file.{Files, Path}

/**
 * The result of parsing the test annotations in a single file.
 *
 * @param errors The errors encountered during parsing.
 * @param annotations The test annotations found.
 */
sealed case class TestAnnotations(
    errors: Seq[TestAnnotationParseError],
    annotations: Seq[TestAnnotation]) {

  def isFileIgnored(file: Path, project: String): Boolean = annotations exists {
    case _: IgnoreFileList => true
    case IgnoreFile(f, _, prj, _) =>
      f.toAbsolutePath == file.toAbsolutePath && prj.equalsIgnoreCase(project)
    case _ => false
  }

  def hasErrors: Boolean = errors.size > 0

  /** Returns all the annotations without IgnoreFile and IgnoreFileList. */
  def outputAnnotations: Seq[LocatedAnnotation] = {
    annotations collect {
      case x: LocatedAnnotation => x
    }
  }

  /**
   * Returns all test annotations except those that are specific
   * to a different project than the given one.
   *
   * @param project the name of the project
   * @return the filtered test annotations
   */
  def filterByProject(project: String): TestAnnotations =
    copy(annotations = annotations filter {
      case a: ProjectSpecificAnnotation => a.project.equalsIgnoreCase(project)
      case _ => true
    })

  /**
   * Returns all test annotations except those output annotations
   * whose key id does not start with the given key id prefix.
   */
  def filterByKeyIdPrefix(keyIdPrefix: String): TestAnnotations =
    copy(annotations = annotations filter {
      case OutputAnnotation(id, _, _) => id.keyId.startsWith(keyIdPrefix)
      case _ => true
    })
}

/** A trait for test annotations. */
sealed trait TestAnnotation

case class OutputAnnotationId(keyId: String, valueId: Option[String]) {
  override def toString = {
    valueId match {
      case None => keyId
      case Some(i) => s"$keyId:$i"
    }
  }

  def matches(id: String): Boolean = {
    val ids = id.split(":")
    if (ids.size == 1) {
      return keyId == id && valueId.isEmpty
    }
    assert(ids.size == 2, s"Expected full ID, but got $id.")
    valueId match {
      case None => keyId == ids(0)
      case Some(s) => keyId == ids(0) && s == ids(1)
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

/**
 * Test annotations that have a location and an identifier
 * (i.e. describe an output of some sort).
 */
sealed trait OutputAnnotation extends LocatedAnnotation {
  def id: OutputAnnotationId

  override def toString = s"$id (${file.getFileName.toString}:$forLineNr)"
}

/**
 * Test annotation that is specific to a certain project.
 * Further details should be given by the referenced issue.
 */
sealed trait ProjectSpecificAnnotation extends TestAnnotation {
  def project: String
  def issueNr: Int
}

object OutputAnnotation {
  def unapply(e: OutputAnnotation) = Some((e.id, e.file, e.forLineNr))
}

case class ExpectedOutput(
    id: OutputAnnotationId,
    file: Path,
    forLineNr: Int,
    annotationLineNr: Int) extends OutputAnnotation

case class UnexpectedOutput(
    id: OutputAnnotationId,
    file: Path,
    forLineNr: Int,
    annotationLineNr: Int,
    project: String,
    issueNr: Int) extends OutputAnnotation with ProjectSpecificAnnotation

case class MissingOutput(
    id: OutputAnnotationId,
    file: Path,
    forLineNr: Int,
    annotationLineNr: Int,
    project: String,
    issueNr: Int) extends OutputAnnotation with ProjectSpecificAnnotation

case class IgnoreOthers(
    file: Path,
    forLineNr: Int,
    annotationLineNr: Int) extends LocatedAnnotation

case class IgnoreFile(
    file: Path,
    annotationLineNr: Int,
    project: String,
    issueNr: Int) extends ProjectSpecificAnnotation

case class IgnoreFileList(
    file: Path,
    annotationLineNr: Int,
    project: String,
    issueNr: Int) extends ProjectSpecificAnnotation
