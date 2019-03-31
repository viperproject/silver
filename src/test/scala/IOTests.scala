// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import java.io.File
import java.nio.file.Paths

import org.scalatest.{FunSuite, Matchers}
import viper.silver.ast.{NoPosition, Position, Program}
import viper.silver.frontend.{SilFrontend, SilFrontendConfig}
import viper.silver.reporter.StdIOReporter
import viper.silver.verifier.errors.ErrorNode
import viper.silver.verifier._

class IOTests extends FunSuite with Matchers {

  val test_prefix = s"Test standard IO of SilFrontend"

  val verifiableFile = "all/basic/let.sil"
  val nonExistingFile = "bla/bla/bla.sil"

  test(s"$test_prefix: some output is produces") {
    runOneCombo(verifiableFile, pass = true, Seq(), Seq())
  }

  test(s"$test_prefix: handling invalid command-line arguments") {
    runOneCombo(verifiableFile, pass = true, Seq("--bla"), Seq("Unknown option"))
  }

  test(s"$test_prefix: handle unreadable file") {
    runOneCombo(nonExistingFile, pass = true, Seq(), Seq("Cannot read"))
  }

  test(s"$test_prefix: handling parseOnly mode and copyright") {
    runOneCombo(verifiableFile, pass = true, Seq("--parseOnly"), Seq("MockIOVerifier 3.14"), Seq(), 1)
  }

  test(s"$test_prefix: external dependencies are reported") {
    runOneCombo(verifiableFile, pass = true, Seq("--dependencies"), Seq("DEP_A", "DEP_B"))
  }

  /* FIXME Currently, SilFrontendConfig.noTiming does not influence anything.
     FIXME StdIOReporter.timeInfo should be set according to it.
  test(s"$test_prefix: --no-timing results in no time info") {
    runOneCombo(verifiableFile, pass = true, Seq("--no-timing"), Seq(), Seq("seconds"))
  }*/

  test(s"$test_prefix: handling PluginException in execute") {
    runOneCombo(verifiableFile, pass = true, Seq("--plugin", "NonExisting.IO.TestPlugin"), Seq("Plugin NonExisting.IO.TestPlugin not found."))
    //runOneCombo(pass = true, Seq("--plugin", "IOTestPlugin"), Seq("Verification successful"))
  }

  test(s"$test_prefix: reporting verification success") {
    runOneCombo(verifiableFile, pass = true, Seq(), Seq("finished verification successfully"))
  }

  test(s"$test_prefix: reporting verification failure") {
    runOneCombo(verifiableFile, pass = false, Seq(), Seq("found 1 error"))
  }

  test(s"$test_prefix: frontend instance is reusable") {
    runOneCombo(verifiableFile, pass = true,  Seq(),              Seq("finished verification successfully"))
    runOneCombo(verifiableFile, pass = false, Seq(),              Seq("found 1 error"))
    runOneCombo(verifiableFile, pass = true,  Seq("--parseOnly"), Seq(), Seq(), 0)
    runOneCombo(verifiableFile, pass = true,  Seq(),              Seq("finished verification successfully"))
  }

  private def runOneCombo(sil_file: String,              // Input Viper program; if does not exist, simulate absent file.
                  pass: Boolean,                         // Decide whether the mock verifier should succeed verification phase.
                  cmd_args: Seq[String],                 // Command line arguments to pass to the verifier.
                  expected_fragments: Seq[String],       // String fragments that must occur in the output.
                  absent_fragments: Seq[String] = Seq(), // String fragments that must not occur in the output.
                  loc: Int = 0) = {                      // Expected number of LOC; below 1 means "don't check."

    (expected_fragments intersect absent_fragments) should be (Seq())

    val resource = getClass.getResource(sil_file)
    val fname = if (resource != null) {
      val file = Paths.get(resource.toURI)
      file.toString
    } else {
      // simulate absent file
      val temp_file = File.createTempFile("io_testing", ".sil")
      val absent_fname = temp_file.getPath
      temp_file.delete()
      absent_fname
    }
    val stream = new java.io.ByteArrayOutputStream()
    Console.withOut(stream) {
      //all printlns in this block will be redirected
      val frontend = new MockIOFrontend(pass)
      frontend.execute(cmd_args :+ fname)
    }

    if (stream.size() == 0)
      fail(s"MockIOFrontend did not produce any output.")
    else {
//      println(s"${stream.toString}") // !! FIXME Please, uncomment me for debugging tests that failed.
//                                     // !! FIXME         Comment me back before you commit the fixes, please.
      val stdoutstr = stream.toString
      expected_fragments.foreach(frag => {
        stdoutstr should include (frag)
      })
      absent_fragments.foreach(frag => {
        stdoutstr should not include (frag)
      })
      if ( loc > 0 ) {
        stdoutstr.split("\r\n|\r|\n").length should be (loc)
      }
    }

  }

  class MockIOFrontend(val pass: Boolean) extends SilFrontend {

    protected var instance: MockIOVerifier = _

    override def createVerifier(fullCmd: String): Verifier = {
      instance = new MockIOVerifier(pass)
      instance
    }

    override def configureVerifier(args: Seq[String]): SilFrontendConfig = {
      instance.parseCommandLine(args)
      instance.config
    }

    override val reporter = StdIOReporter("MockStdIOReporter")
  }

  class MockIOVerifier(val pass: Boolean) extends Verifier {

    private var _config: MockIOConfig = _

    def config: MockIOConfig = _config

    override def name: String = "MockIOVerifier"

    override def version: String = "3.14"

    override def buildVersion: String = "2.72"

    override def copyright: String = "(c) Copyright ETH Zurich 2012 - 2018"

    override def debugInfo(info: Seq[(String, Any)]): Unit = {}

    override def dependencies: Seq[Dependency] = List(
      new Dependency {
        def name = "DEP_A"
        def version = "1.2.3"
        def location = "mock_location/dep_a"
      },
      new Dependency {
        def name = "DEP_B"
        def version = "4.5.6"
        def location = "mock_location/dep_b"
      })

    override def parseCommandLine(args: Seq[String]): Unit = {
      _config = new MockIOConfig(args)
    }

    override def start(): Unit = {}

    override def verify(program: Program): VerificationResult = {
      if (pass) Success
      else Failure(Seq(new VerificationError {
        override def reason: ErrorReason = DummyReason
        override def readableMessage(withId: Boolean, withPosition: Boolean): String =
          "MockIOVerifier failed the verification (as requested)."
        override def withNode(offendingNode: ErrorNode): ErrorMessage = DummyReason
        override def pos: Position = NoPosition
        override def offendingNode: ErrorNode = DummyNode
        override def id: String = "MockIOVerifier.verification.failure"
      }))
    }

    override def stop(): Unit = {}
  }

  class MockIOConfig(args: Seq[String]) extends SilFrontendConfig(args, "MockIOVerifier") {
    verify()
  }
}
