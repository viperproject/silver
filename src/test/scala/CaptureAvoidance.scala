// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import viper.silver.frontend._
import viper.silver.verifier.Verifier
import org.scalatest.FunSuite
import java.nio.file.Paths

class CaptureAvoidance extends FunSuite {

  object frontend extends SilFrontend {
    def configureVerifier(args: Seq[String]): SilFrontendConfig = ???
    def createVerifier(fullCmd: String): Verifier = ???

    def semanticAnalysis(filename: String): Unit = {
      val path = Paths.get(getClass.getResource(filename).toURI)
      _state = DefaultStates.Initialized
      reset(path)
      runTo("Semantic Analysis")
      assert(_errors.isEmpty, "Unexpected errors occurred in the semantic analysis of capture avoidance tests.")
    }
  }

  test("Checking enforcement of rule 1 of capture avoidance") {
    frontend.semanticAnalysis("capture_avoidance/capture_avoidance_rule_1.vpr")
  }

//test("Checking enforcement of rule 2 of capture avoidance") {
//  // TODO: This should be a call to verifier if willing to see an error. Or some other way to simulate replacement?
//  frontend.semanticAnalysis("capture_avoidance/capture_avoidance_rule_2.vpr")
//}

  //? test("Checking enforcement of rule 3 of capture avoidance") {
  //?   frontend.semanticAnalysis("capture_avoidance/capture_avoidance_rule_3.vpr")
  //? }
}
