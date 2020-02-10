// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.predicateinstance

import fastparse.noApi
import viper.silver.ast.{Domain, DomainType, ErrTrafo, FuncApp, Function, Position, PredicateAccess, PredicateAccessPredicate, Program, WildcardPerm}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{ConsistencyError, Failure, Success, VerificationResult}
import viper.silver.verifier.errors.PreconditionInAppFalse


class PredicateInstancePlugin  extends SilverPlugin with ParserPluginTemplate {

  /**
   * Syntactic marker for predicate instances
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

  /**
   * Generate for predicates the predicate instance function.
   * Transform predicate instances AST nodes into function calls
   * (to the respective predicate instance functions)
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
    newProgram
  }

  /**
   * Initiate the error transformer for possibly predicate instances related errors
   */
  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Success => input
      case Failure(errors) =>
        Failure(errors.map {
          case e@PreconditionInAppFalse(_, _, _) => e.transformedError()
          case e => e
        })
    }
  }

  private def reportPredicateInstanceNotDefined(pos: Position): Unit = {
    reportError(ConsistencyError("PredicateInstance domain is needed but not declared.", pos))
  }

  private val errT = ErrTrafo({
    case PreconditionInAppFalse(offendingNode, reason, cached) => PredicateInstanceNoAccess(offendingNode, reason, cached)
  })

}