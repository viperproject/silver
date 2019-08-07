// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver

import viper.silver.frontend._
import viper.silver.verifier.Verifier
import org.scalatest.FunSuite
import java.nio.file.Paths

class CaptureAvoidance extends FunSuite {

  object frontend extends SilFrontend {
    def configureVerifier(args: Seq[String]): SilFrontendConfig = ???
    def createVerifier(fullCmd: String): Verifier = ???
  }

  test("Verify all programs in capture avoidance directory") {
    val filename = "capture_avoidance/capture_avoidance_rule_1.sil"
    val path = Paths.get(getClass.getResource(filename).toURI)
    frontend.reset(path)
    frontend.runTo("Semantic Analysis")
  }
}
