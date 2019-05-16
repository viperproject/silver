// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import java.nio.file.{Path, Paths}

import org.scalatest.Suite
import viper.silver.ast.{Node, Program}
import viper.silver.ast.utility.rewriter.StrategyInterface
import viper.silver.frontend.{SilFrontend, SilFrontendConfig, DefaultStates}
import viper.silver.verifier.{AbstractError, Verifier}

object TestHelpers {
  class MockSilFrontend extends SilFrontend {
    def createVerifier(fullCmd: _root_.scala.Predef.String): Verifier = ???

    def configureVerifier(args: Seq[String]): SilFrontendConfig = ???

    def translate(silverFile: Path): (Option[Program], Seq[AbstractError]) = {
      _verifier = None
      _state = DefaultStates.Initialized

      reset(silverFile)
      runTo("Translation")

      (_program, _errors)
    }
  }

  // From: http://biercoff.com/easily-measuring-code-execution-time-in-scala/
  def time[R](block: => R): R = {
    val t0 = System.nanoTime()
    val result = block    // call-by-name
    val t1 = System.nanoTime()

    // println("Elapsed time: " + (t1 - t0) + "ns")

    result
  }

  trait FileComparisonHelper { this: Suite =>
    def executeTest(filePrefix: String,
                    fileName: String,
                    strat: StrategyInterface[Node],
                    frontend: MockSilFrontend)
                   : Unit = {

      val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
      assert(fileRes != null, s"File $filePrefix$fileName not found")
      val file = Paths.get(fileRes.toURI)
      var targetNode: Node = null
      var targetRef: Node = null

      frontend.translate(file) match {
        case (Some(p), _) => targetNode = p
        case (None, errors) =>
          fail(s"Problem with program $file: $errors")
      }
      val res = strat.execute[Program](targetNode)

      val fileRef = getClass.getResource(filePrefix + fileName + "Ref.sil")
      assert(fileRef != null, s"File $filePrefix$fileName Ref not found")

      val ref = Paths.get(fileRef.toURI)
      frontend.translate(ref) match {
        case (Some(p), _) => targetRef = p
        case (None, errors) => fail("Problem with program: " + errors)
      }

      val obtainedOutput = res.toString()
      val expectedOutput = targetRef.toString()

      assert(
        obtainedOutput == expectedOutput,
        s"""Transformation of program $fileRes did not yield expected program $fileRef:
           |------Got ------
           |$obtainedOutput
           |--- Expected ---
           |$expectedOutput
         """.stripMargin)
    }
  }
}
