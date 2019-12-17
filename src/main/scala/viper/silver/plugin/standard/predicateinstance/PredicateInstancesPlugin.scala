// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import fastparse.noApi
import viper.silver.ast.{Assert, Exp, FalseLit, Function, Method, Or, Position, PredicateAccess, PredicateAccessPredicate, Program, TrueLit, While}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.errors.AssertFailed
import viper.silver.verifier.{AbstractError, ConsistencyError, Failure, Success, VerificationError, VerificationResult}

class PredicateInstancesPlugin  extends SilverPlugin with ParserPluginTemplate {

  /**
   * Keyword used to define decreases clauses
   */
  val PredicateInstanceMarker: String = "@"

  import White._
  import fastparse.noApi._

  /**
   * Parser for declaring predicate instances.
   *
   */
    lazy val predicateInstance: noApi.P[PPredicateInstance] = P(PredicateInstanceMarker ~/ P(predAcc)).map(p => PPredicateInstance(p.args, p.idnuse))

  /** Called before any processing happened.
   *
   * @param input      Source code as read from file
   * @param isImported Whether the current input is an imported file or the main file
   * @return Modified source code
   */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewExpAtStart(predicateInstance)
    input
  }
}