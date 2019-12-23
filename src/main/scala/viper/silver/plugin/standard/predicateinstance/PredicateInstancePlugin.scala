// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import fastparse.noApi
import viper.silver.ast.{Domain, DomainType, ErrTrafo, FuncApp, Function, NodeTrafo, Position, PredicateAccess, PredicateAccessPredicate, Program, WildcardPerm}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{ConsistencyError, Failure, Success, VerificationResult}
import viper.silver.verifier.errors.PreconditionInAppFalse


class PredicateInstancePlugin  extends SilverPlugin with ParserPluginTemplate {

  /**
   * Keyword used to define decreases clauses
   */
  val PredicateInstanceMarker: String = "@"

  val PredicateInstanceDomainName = "PredicateInstance"

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

  /** Called after methods are filtered but before the verification by the backend happens.
   *
   * @param input AST
   * @return Modified AST
   */
  override def beforeVerify(input: Program): Program = {
    val PredicateInstanceDomain: Option[Domain] =  input.domains.find(_.name == "PredicateInstance")

    // list of all created predicate instance functions
    val createdPIFunctions: collection.mutable.ListMap[String, Function] = collection.mutable.ListMap[String, Function]()

    def getPIFunction(predicateInstance: PredicateInstance, program: Program): FuncApp = {
      createdPIFunctions.get(predicateInstance.p) match {
        case Some(piFunction) => FuncApp(piFunction, predicateInstance.args)(predicateInstance.pos, predicateInstance.info, errT)
        case None =>
          val piFunctionName = s"PI_${predicateInstance.p}"
          val pred = program.findPredicate(predicateInstance.p)
          val newPIFunction =
            Function(piFunctionName,
              pred.formalArgs,
              DomainType(PredicateInstanceDomain.get, Map()),
              Seq(PredicateAccessPredicate(PredicateAccess(pred.formalArgs.map(_.localVar), pred.name)(), WildcardPerm()())(predicateInstance.pos, predicateInstance.info, predicateInstance.errT)),
              Seq(),
              None
            )(PredicateInstanceDomain.get.pos, PredicateInstanceDomain.get.info)
          createdPIFunctions.update(predicateInstance.p, newPIFunction)
          FuncApp(newPIFunction, predicateInstance.args)(predicateInstance.pos, predicateInstance.info, errT)
      }
    }

    val newProgram: Program = ViperStrategy.Slim({
      case pi: PredicateInstance =>
        if (PredicateInstanceDomain.isEmpty){
          reportPredicateInstanceNotDefined(pi.pos)
          pi
        } else {
          getPIFunction(pi, input)
        }
      case p: Program =>
        p.copy(functions = p.functions ++ createdPIFunctions.values)(p.pos, p.info, p.errT)
    }, Traverse.BottomUp).execute(input)

    println(newProgram)

    newProgram
  }

  /** Called after the verification. Error transformation should happen here.
   * This will only be called if verification took place.
   *
   * @param input Result of verification
   * @return Modified result
   */
  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Success => input
      case Failure(errors) => {
        Failure(errors.map {
          case e@PreconditionInAppFalse(_, _, _) => e.transformedError()
          case e => e
        })
      }
    }
  }

  private def reportPredicateInstanceNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("PredicateInstance domain is needed but not declared.", pos))
  }

  private val errT = ErrTrafo({
    case PreconditionInAppFalse(offendingNode, reason, cached) => PredicateInstanceNoAccess(offendingNode, reason, cached)
  })

}