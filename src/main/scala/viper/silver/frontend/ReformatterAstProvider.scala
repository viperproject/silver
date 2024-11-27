// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.frontend
import viper.silver.parser.PProgram
import viper.silver.reporter.Reporter
import viper.silver.verifier.{Failure, Success, VerificationResult}

class ReformatterAstProvider(override val reporter: Reporter) extends ViperAstProvider(reporter) {
  override val phases: Seq[Phase] = Seq(Parsing)

  override def doParsing(input: String): Result[PProgram] = parsingInner(input, false)

  override def result: VerificationResult = {

    if (_errors.isEmpty) {
      require(state >= DefaultStates.Parsing)
      Success
    }
    else {
      Failure(_errors)
    }
  }
}
