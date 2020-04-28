// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import viper.silver.ast._
import viper.silver.verifier.AbstractError

/**
 * Trafo combines the ProgramManager (which manages name conflicts) with
 * FunctionCheck (which generates termination checks for functions) and
 * MethodCheck (which generates termination checks for methods and whiles)
 *
 * @param program     The program to be extended with termination checks.
 * @param reportError Interface to report errors occurring during transformation.
 */
final class Trafo(override val program: Program,
                  override val reportError: AbstractError => Unit)
  extends ProgramManager with FunctionCheck with MethodCheck {

  private var transformedProgram: Option[Program] = None

  /**
   * @return the program including the termination checks.
   */
  def getTransformedProgram: Program = {
    transformedProgram.getOrElse({

      val proofMethods: Seq[Method] = program.functions.flatMap(generateProofMethods)
      val newMethods: Seq[Method] = program.methods.map(transformMethod)

      val newProgram: Program = program.copy(methods = newMethods ++ proofMethods)(program.pos, program.info, program.errT)
      transformedProgram = Some(newProgram)

      newProgram
    })
  }
}