/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package  semper.sil.testing

import java.nio.file.{Files, Path}
import io.Source
import semper.sil.verifier.Verifier
import semper.sil.frontend.Frontend

/** A sil suite that can only handle single files. */
trait SingleFileSilSuite extends SilSuite {

  /** The frontend to be used. */
  def frontend(verifier: Verifier, files: Seq[Path]): Frontend = files match {
    case file :: Nil => frontend(verifier, Source.fromInputStream(Files.newInputStream(file)).mkString)
    case _ => sys.error("This suite can only handle one file per test.")
  }

  /** The frontend to be used. */
  def frontend(verifier: Verifier, input: String): Frontend

  override def buildTestInput(file: Path, prefix: String) =
    super.buildTestInput(file, prefix).copy(files = Seq(file))
}
