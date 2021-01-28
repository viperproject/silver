// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.testing

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
      f.toAbsolutePath == file.toAbsolutePath && projectNameMatches(prj, project) //prj.equalsIgnoreCase(project)
    case _ => false
  }

  def hasErrors: Boolean = errors.nonEmpty

  /** Returns all the annotations without IgnoreFile and IgnoreFileList. */
  def outputAnnotations: Seq[LocatedAnnotation] = {
    annotations collect {
      case x: LocatedAnnotation => x
    }
  }

  /* [2014-07-14 Malte]
   *   ProjectSpecificAnnotations include a project name, e.g., Silicon,
   *   and this case should return true iff the name of the current
   *   project under testing matches the project name that is part of the
   *   annotation. This ensures that, e.g., UnexpectedOutput-annotations
   *   are only "expected" when the corresponding project is tested.
   *
   *   Having different forks of a project unfortunately complicates the
   *   name comparison because the forks might have different names.
   *   E.g., assume that there is a fork if Silicon called Silicon-Foo.
   *   While the fork is being developed it gets its own test cases,
   *   which are specific to this fork and not intended for its upstream.
   *   These tests may have project-specific annotations, which include
   *   the fork's project name, i.e., "Silicon-Wands".
   *   All tests coming from of the upstream, however, still include the
   *   original project name ("Silicon"), which doesn't match the fork's
   *   name, with the consequence that all upstream tests with project-
   *   specific annotations fails.
   *
   *   To account for forks with different names, the name comparison
   *   (which used to be a.project.equalsIgnoreCase(project)) has been
   *   changed s.t. it ignores the string preceding/following the project
   *   name IF it is separated by a hyphen.
   *
   *   Examples:
   *
   *   Let "silicon" be the project name included in an annotation.
   *   The following project names will/won't match:
   *      will:  silicon, Silicon, silicon-Wands, magic-wands-silicon-2
   *      won't: sil, sil-wands
   *
   *   Let "sil" be the project name included in an annotation:
   *      will:  sil, sil-wands
   *      won't: silicon, Silicon, silicon-Wands, magic-wands-silicon-2
   *
   *   Let "silicon-wands" be the project name included in an annotation:
   *     will:  silicon-Wands
   *     won't: silicon, sil, Silicon, magic-wands-silicon-2, sil-wands
   */
  def projectNameMatches(annotationProject: String, currentProject: String): Boolean =
    currentProject.matches(s"(?i)(.*?-)?$annotationProject(-.*?)?")

  /**
   * Returns all test annotations except those that are specific
   * to a different project than the given one.
   *
   * @param projectInfo project names
   * @return the filtered test annotations
   */
  def filterByProject(projectInfo: ProjectInfo): TestAnnotations =
    copy(annotations = annotations filter {
      case a: ProjectSpecificAnnotation =>
        projectInfo.projectNames.exists(projectNameMatches(a.project, _))
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
    assert(ids.size >= 2, s"Expected full ID, but got $id.")
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
}

/**
 * Test annotations that have a location and an identifier
 * (i.e. describe an output of some sort).
 */
sealed trait OutputAnnotation extends LocatedAnnotation {
  def id: OutputAnnotationId

  def sameSource(other: OutputAnnotation) =
    Files.isSameFile(this.file, other.file) && forLineNr == other.forLineNr && this.id == other.id

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
