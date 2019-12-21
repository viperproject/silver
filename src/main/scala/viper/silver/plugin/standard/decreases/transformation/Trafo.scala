// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.decreases.transformation

import viper.silver.ast._
import viper.silver.verifier.AbstractError

final class Trafo(override val program: Program,
            override val reportError: AbstractError => Unit)
  extends ProgramManager with ErrorReporter with FunctionCheck with MethodCheck {


  var transformedProgram: Option[Program] = None

  def getTransformedProgram: Program = {
    transformedProgram.getOrElse({
      generateProofMethods()
      transformMethods()
      val newProgram = generateCheckProgram()
      transformedProgram = Some(newProgram)
      newProgram
    })
  }
}