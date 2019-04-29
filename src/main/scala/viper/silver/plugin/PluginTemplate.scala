// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import viper.silver.ast.Program
import viper.silver.parser.PProgram
import viper.silver.verifier.{AbstractError, VerificationResult}

// The aim of this file is just to give a skeleton implementation to copy for a particular plugin implementation.
//
// This class copies all interface methods from the SilverPlugin trait. For a concrete plugin, it is typically
// unnecessary to define *all* of these methods; those for which no special implementation is needed can be simply
// deleted; the default implementations in SilverPlugin should suffice.
class PluginTemplate extends SilverPlugin {
    /** Called before any processing happened.
      *
      * @param input Source code as read from file
      * @param isImported Whether the current input is an imported file or the main file
      * @return Modified source code
      */
    override def beforeParse(input: String, isImported: Boolean) : String = ???

    /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
      *
      * @param input Parse AST
      * @return Modified Parse AST
      */
    override def beforeResolve(input: PProgram) : PProgram = ???

    /** Called after identifiers have been resolved but before the parse AST is translated into the normal AST.
      *
      * @param input Parse AST
      * @return Modified Parse AST
      */
    override def beforeTranslate(input: PProgram): PProgram = ???

    /** Called after parse AST has been translated into the normal AST but before methods to verify are filtered.
      * In [[viper.silver.frontend.SilFrontend]] this step is confusingly called doTranslate.
      *
      * @param input AST
      * @return Modified AST
      */
    override def beforeMethodFilter(input: Program) : Program = ???

    /** Called after methods are filtered but before the verification by the backend happens.
      *
      * @param input AST
      * @return Modified AST
      */
    override def beforeVerify(input: Program) : Program = ???

    /** Called after the verification. Error transformation should happen here.
      * This will only be called if verification took place.
      *
      * @param input Result of verification
      * @return Modified result
      */
    override def mapVerificationResult(input: VerificationResult): VerificationResult = ???

    /** Called after the verification just before the result is printed. Will not be called in tests.
      * This will also be called even if verification did not take place (i.e. an error during parsing/translation occurred).
      *
      * @param input Result of verification
      * @return Modified result
      */
    override def beforeFinish(input: VerificationResult) : VerificationResult = ???

    /** Can be called by the plugin to report an error while transforming the input.
      *
      * The reported error should correspond to the stage in which it is generated (e.g. no ParseError in beforeVerify)
      *
      * @param error The error to report
      */
    override def reportError(error: AbstractError): Unit = ???
}
