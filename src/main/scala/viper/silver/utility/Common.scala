// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import java.io.{
  File => JFile,
  PrintWriter => JPrintWriter,
  BufferedWriter => JBufferedWriter,
  FileWriter => JFileWriter}

/** Utilities that are not tied to Silver itself.
  *
  * TODO: Move into a 'common' sub-project inside Silver (similar to Silicon's
  *       'common' sub-project). If done, consider introducing sub-packages,
  *       for example, 'io'.
  */
object Common {

  /* Utilities simplifying using Scala */

  trait StructuralEquality { self: AnyRef =>
    protected val equalityDefiningMembers: Seq[Any]

    override val hashCode = generateHashCode(equalityDefiningMembers)

    override def equals(other: Any) = (
         this.eq(other.asInstanceOf[AnyRef])
      || (other match {
            case se: StructuralEquality if this.getClass.eq(se.getClass) =>
              equalityDefiningMembers == se.equalityDefiningMembers
            case _ => false
          }))
  }

  /* Take from scala -print when working with case classes. */
  @inline
  def generateHashCode(xs: Any*) = {
    var code = 0

    for (x <- xs)
      code = code * 41 + (if (x == null) 0 else x.##)

    code
  }

  /* Utilities related to I/O */

  /**
   * Writes the `contents` to the given `file`. Existing content will be overwritten.
   *
   * @param contents The content to write.
   * @param file The file to which the content will be written.
   */
  def toFile(contents: String, file: JFile) {
    val sink = PrintWriter(file)

    sink.write(contents)
    sink.close()
  }

  /** Creates a `java.io.PrintWriter` with `autoFlush` enabled that writes to the given `file`.
    * `File.mkdirs()` is called to ensure that the file path exists.
    *
    * @param file Is assumed to denote a file, not a directory.
    * @param autoFlush Passed on to Java's `PrintWriter`.
    * @param append Passed on to Java's `FileWriter`.
    * @return The instantiated sink.
    */
  def PrintWriter(file: JFile, autoFlush: Boolean = true, append: Boolean = false): JPrintWriter = {
    val pf = file.getParentFile
    if (pf != null) pf.mkdirs()

    new JPrintWriter(new JBufferedWriter(new JFileWriter(file, append)), autoFlush)
  }
}
