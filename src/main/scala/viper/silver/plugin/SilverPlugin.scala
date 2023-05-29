// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import ch.qos.logback.classic.Logger
import viper.silver.ast.Program
import viper.silver.frontend.SilFrontendConfig
import viper.silver.parser.{FastParser, PProgram}
import viper.silver.reporter.{Entity, Reporter}
import viper.silver.verifier.{AbstractError, VerificationResult}

import scala.annotation.unused

/** Implement this abstract class in order to give your plugin access to SilFrontend's IO:
  * 1. Reporter,
  * 2. Logger,
  * 3. Command line arguments, and
  * 4. Parser.
  * Has to be set as an explicit parameter for the plugin constructor.
  */
trait IOAwarePlugin {
  val reporter: Reporter
  val logger: Logger
  val cmdArgs: SilFrontendConfig
  val fp: FastParser
}

/** Trait to be extended by plugins. A plugin can change the current structure of the program under verification
  * at several hooks. The plugin gets the current state and has to return a new (maybe modified) state.
  */
trait SilverPlugin {

  protected var _errors: Seq[AbstractError] = Seq()
  def errors: Seq[AbstractError] = _errors

  /** Called before any processing happened.
    *
    * @param input Source code as read from file
    * @param isImported Whether the current input is an imported file or the main file
    * @return Modified source code
    */
  def beforeParse(input: String, @unused isImported: Boolean): String = input

  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  def beforeResolve(input: PProgram): PProgram = input

  /** Called after identifiers have been resolved but before the parse AST is translated into the normal AST.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  def beforeTranslate(input: PProgram): PProgram = input

  /** Called after parse AST has been translated into the normal AST but before methods to verify are filtered.
    * In [[viper.silver.frontend.SilFrontend]] this step is confusingly called doTranslate.
    *
    * @param input AST
    * @return Modified AST
    */
  def beforeMethodFilter(input: Program) : Program = input

  /** Called after methods are filtered but before the verification by the backend happens.
    *
    * @param input AST
    * @return Modified AST
    */
  def beforeVerify(input: Program) : Program = input

  /** Called after the verification of an entity, which is used to stream verification results to the IDE
    * (which happens as soon as a member has been verified). Error transformation should happen here.
    * This will only be called if verification of `entity` took place.
    *
    * @param entity Entity to which `input` belongs
    * @param input Result of verification
    * @return Modified result
    */
  def mapEntityVerificationResult(@unused entity: Entity, input: VerificationResult): VerificationResult = input

  /** Called after the verification. Error transformation should happen here.
    * This will only be called if verification took place.
    *
    * @param program Viper AST
    * @param input Result of verification
    * @return Modified result
    */
  def mapVerificationResult(@unused program: Program, input: VerificationResult): VerificationResult = input

  /** Called after the verification just before the result is printed. Will not be called in tests.
    * This will also be called even if verification did not take place (i.e. an error during parsing/translation occurred).
    *
    * @param input Result of verification
    * @return Modified result
    */
  def beforeFinish(input: VerificationResult) : VerificationResult = input

  /** Can be called by the plugin to report an error while transforming the input.
    *
    * The reported error should correspond to the stage in which it is generated (e.g. no ParseError in beforeVerify)
    *
    * @param error The error to report
    */
  def reportError(error: AbstractError): Unit ={
    if (!_errors.exists(e => e == error && e.pos == error.pos)) {
      _errors :+= error
    }
  }

}
