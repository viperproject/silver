/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast.Program
import viper.silver.parser.PProgram
import viper.silver.verifier.VerificationResult

/** Trait to be extended by plugins. A plugin can change the current structure of the program under verification
  * at several hooks. The plugin gets the current state and has to return a new (maybe modified) state.
  */
trait SilverPlugin {

  /** Called before any processing happened.
    *
    * @param input Source code as read from file
    * @return Modified source code
    */
  def beforeParse(input: String) : String = input

  /** Called after parse AST has been constructed but before identifiers are resolved.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  def beforeResolve(input: PProgram) : PProgram = input

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

  /** Called after the verification just before the result is printed. Error transformation should happen here.
    *
    * @param input Result of verification
    * @return Modified result
    */
  def beforeFinish(input: VerificationResult) : VerificationResult = input

}
