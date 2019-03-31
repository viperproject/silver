// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.testing

import java.nio.file.{Files, Path}
import java.util.regex.Pattern
import org.scalatest.Tag
import scala.collection.JavaConverters._

/** Provides the name, files and tags from which to create a test. */
trait TestInput {
  /** The name of the test, e.g. the name of the canonical source file. */
  val name: String

  /** Zero or more parent folders of the test file. */
  val prefix: String

  /** The list of files which belong to the same test as the given file. */
  val files: Seq[Path]

  /** The canonical test source file. */
  def file: Path = files.head

  /** The tags to be used for the test. */
  val tags: Seq[Tag]
}

case class DefaultTestInput(
    name: String,
    prefix: String,
    files: Seq[Path],
    tags: Seq[Tag]) extends TestInput {}

object DefaultTestInput {
  val fileListRegex = """(.*)_file\d*.*""".r

  /**
   * Creates the default test input from the given source file and prefix.
   *
   * It is possible to create a single test with multiple files by naming
   * the files foo_file1.ext foo_file2.ext etc. and putting them into
   * the same directory. They are ordered according to their number.
   *
   * Tests are named by their first file, e.g. `basic/functions.silver`. Tests are
   * also tagged by their name and their file name (with and without extension):
   * In the example the tags would be `basic/functions.silver`, `functions.silver` and
   * `functions`. These tags can be used to execute just a single test:
   * `test-only * -- -n functions`.
   *
   * @param file the canonical test file representing the test
   * @param prefix zero or more parent folders of the test file
   */
  def apply(file: Path, prefix: String): DefaultTestInput = {
    val name = file.getFileName.toString match {
      case fileListRegex(n) => prefix + "/" + n
      case n => prefix + "/" + n
    }

    val files: Seq[Path] = file.toString match {
      case fileListRegex(n) =>
        // Create a regex for files that belong to the same test.
        val regex = (Pattern.quote(n) + """_file(\d*).*""").r
        // Collect all files that match this regex and their numbers.
        var files = List[(Path, Int)]()
        val dirStream = Files.newDirectoryStream(file.getParent)
        dirStream.asScala foreach { f =>
          f.toString match {
            case regex(index) => files = (f, index.toInt) :: files
            case _ =>
          }
        }
        // Sort the file by their numbers and return the files only.
        // (We only needed the numbers for ordering)
        files.sortBy(_._2).map(_._1)
      case _ => List(file)
    }

    val tags: Seq[Tag] = {
      val relativeFileName = prefix + "/" + file.getName(file.getNameCount - 1)
      val fileName = file.getFileName.toString
      val fileNameWithoutExt = fileName.substring(0, fileName.lastIndexOf("."))

      val prefixes = relativeFileName.split("[/\\\\]").dropRight(1).inits.map(p => Tag(p.mkString("","/","/")))

      List(
        Tag(relativeFileName),
        Tag(file.toString),
        Tag(fileName),
        Tag(fileNameWithoutExt)) ++ prefixes
    }

    DefaultTestInput(name, prefix, files, tags)
  }
}
