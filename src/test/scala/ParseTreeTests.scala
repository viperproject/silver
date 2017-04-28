/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import java.nio.file.Paths

import TestHelpers.MockSilFrontend
import org.scalatest.FunSuite
import viper.silver.ast._

import scala.language.implicitConversions

class ParseTreeTests extends FunSuite {
  test("CyclicMacroDetection") {
    val filePrefix = "parsertests/cyclicMacros/"
    val files = Seq("simple", "complex", "complexExp")

    val frontend = new MockSilFrontend

    files foreach {
      fileName => {
        val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
        assert(fileRes != null, s"File $filePrefix$fileName not found")
        val file = Paths.get(fileRes.toURI)

        frontend.translate(file) match {
          case (Some(_), _) =>
            fail("Expected cyclic macro errors, but gone none")
          case (None, errors) => errors.foreach(e => {
            assert(e.readableMessage.contains("Recursive macro declaration found"))
          })
        }
      }
    }
  }

  test("MacroExpansion") {
    val filePrefix = "parsertests/macroExpansion/"
    val files = Seq("simple", "simple2", "simpleExp", "simpleArgs", "simpleArgs2", "simpleArgsExp", "simpleMethod", "simpleMethodExp")

    val frontend = new MockSilFrontend

    files foreach(fileName =>
      parseAndCompare(filePrefix + fileName + ".sil", filePrefix + fileName + "Ref" + ".sil", frontend))
  }

  test("HygienicMacros") {
    val filePrefix = "parsertests/hygienicMacros/"
    val files = Seq("simple", "nested", "collision", "collision2", "forall", "loopConstruction")

    val frontend = new MockSilFrontend

    files foreach (fileName =>
      parseAndCompare(filePrefix + fileName + ".sil", filePrefix + fileName + "Ref" + ".sil", frontend))
  }

  test("Imports") {
    val filePrefix = "parsertests/imports/"
    val files = Seq("simple", "complex", "cyclic")

    val frontend = new MockSilFrontend

    files foreach (fileName =>
      parseAndCompare(filePrefix + fileName + ".sil", filePrefix + fileName + "Ref" + ".sil", frontend))
  }

  private def parseAndCompare(testFile: String, refFile: String, frontend: MockSilFrontend): Unit = {
    val fileRes = getClass.getResource(testFile)
    assert(fileRes != null, s"File $testFile not found")
    val file = Paths.get(fileRes.toURI)

    val fileRef = getClass.getResource(refFile)
    assert(fileRef != null, s"File $refFile not found")
    val fileR = Paths.get(fileRef.toURI)

    var targetNode: Node = null
    var targetRef: Node = null

    frontend.translate(file) match {
      case (Some(p), _) => targetNode = p
      case (None, errors) => sys.error("Error occurred during translating: " + errors)
    }

    frontend.translate(fileR) match {
      case (Some(p), _) => targetRef = p
      case (None, errors) => sys.error("Error occurred during translating: " + errors)
    }

    val obtainedOutput = targetNode.toString()
    val expectedOutput = targetRef.toString()

    assert(obtainedOutput == expectedOutput,
           s"""Transformation of program $fileRes did not yield expected program $fileRef:
              |------Got ------
              |$obtainedOutput
              |--- Expected ---
              |$expectedOutput
            """.stripMargin)
  }
}
