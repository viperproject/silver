// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import java.nio.file.Paths
import TestHelpers.MockSilFrontend
import org.scalatest.FunSuite
import viper.silver.ast._

class ParseTreeTests extends FunSuite {
  test("MacroExpansion") {
    val filePrefix = "transformations/Macros/Expansion/"
    val files = Seq("simple", "simple2", "simpleExp", "simpleArgs", "simpleArgs2", "simpleArgsExp", "simpleMethod", "simpleMethodExp")

    val frontend = new MockSilFrontend

    files foreach(fileName =>
      parseAndCompare(filePrefix + fileName + ".sil", filePrefix + fileName + "Ref" + ".sil", frontend))
  }

  test("HygienicMacros") {
    val filePrefix = "transformations/Macros/Hygienic/"
    val files = Seq("simple", "nested", "collision", "collision2", "forall", "loopConstruction")

    val frontend = new MockSilFrontend

    files foreach (fileName =>
      parseAndCompare(filePrefix + fileName + ".sil", filePrefix + fileName + "Ref" + ".sil", frontend))
  }

  test("Positions and Paths") {
    val filePrefix = "transformations/Imports/"
    val files = Seq("simpleRef", "simple_other")

    val paths: Seq[String] = files.map { f => filePrefix + f + ".sil" }

    val fileResA = getClass.getResource(paths.head)
    assert(fileResA != null, s"File ${paths.head} not found")
    val file_a = Paths.get(fileResA.toURI)

    val fileResB = getClass.getResource(paths(1))
    assert(fileResB != null, s"File ${paths(1)} not found")
    val file_b = Paths.get(fileResB.toURI)

    val frontend_a = new MockSilFrontend
    val frontend_b = new MockSilFrontend

    frontend_a.translate(file_a) match {
      case (Some(prog_a), _) =>
        frontend_b.translate(file_b) match {
          case (Some(prog_b), _) =>
            prog_a.members.foreach(m_1 =>
              m_1.pos match {
                case p_1: AbstractSourcePosition =>
                  prog_b.members.foreach(m_2 =>
                    m_2.pos match {
                      case p_2: AbstractSourcePosition =>
                        assert(p_1.file.toUri.compareTo(p_2.file.toUri) != 0,
                               s"""Given that there are no import statements in the programs:
                                 | Prog A: ${fileResA.toURI}
                                 | Prog B: ${fileResB.toURI}
                                 | the absolute paths in the positions of AST nodes from these files
                                 | must be different.""".stripMargin)
                      case NoPosition =>
                        assert(m_2.info.getUniqueInfo[Synthesized.type].isDefined,
                               "positions of AST nodes are not set by the parser")
                      case other =>
                        fail(s"Found unexpected position node $other (${other.getClass.getName})")
                    })
                case NoPosition =>
                  assert(m_1.info.getUniqueInfo[Synthesized.type].isDefined,
                         "positions of AST nodes are not set by the parser")
                case other =>
                  fail(s"Found unexpected position node $other (${other.getClass.getName})")
              })
          case (None, errors) => sys.error("Error occurred during translating: " + errors)
        }
      case (None, errors) => sys.error("Error occurred during translating: " + errors)
    }
  }

  test("Imports") {
    val filePrefix = "transformations/Imports/"
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
