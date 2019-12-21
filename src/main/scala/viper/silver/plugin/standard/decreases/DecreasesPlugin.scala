// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.decreases

import fastparse.noApi
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.{Assert, Exp, Function, Method, Position, Program, While}
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.standard.decreases.transformation.Trafo
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.errors.AssertFailed
import viper.silver.verifier._

class DecreasesPlugin(reporter: viper.silver.reporter.Reporter,
                      logger: ch.qos.logback.classic.Logger,
                      config: viper.silver.frontend.SilFrontendConfig)  extends SilverPlugin with ParserPluginTemplate {

  private val deactivated = if(config != null) config.decreases.toOption.getOrElse(false) else false

  /**
   * Keyword used to define decreases clauses
   */
  private val DecreasesKeyword: String = "decreases"

  import White._
  import fastparse.noApi._

  /**
   * Parser for decreases clauses with following possibilities.
   *
   * decreases exp (, exp)* (if exp)?
   * or
   * decreases _ (if exp)?
   * or
   * decreases *
   */
  lazy val decreases: noApi.P[PDecreasesExp] =
    P(keyword(DecreasesKeyword) ~/ (decreasesWildcard|decreasesStar|decreasesTuple) ~ ";".?)
  lazy val decreasesTuple: noApi.P[PDecreasesTuple] =
    P(exp.rep(sep=",") ~/ condition.?).map {case (a, c) => PDecreasesTuple(a,c) }
  lazy val decreasesWildcard: noApi.P[PDecreasesWildcard] = P("_" ~/ condition.?).map(c => PDecreasesWildcard(c))
  lazy val decreasesStar: noApi.P[PDecreasesStar] = P("*").map(_ => PDecreasesStar())
  lazy val condition: noApi.P[PExp] = P("if" ~/ exp)

  /** Called before any processing happened.
   *
   * @param input      Source code as read from file
   * @param isImported Whether the current input is an imported file or the main file
   * @return Modified source code
   */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String](DecreasesKeyword))
    // Add new parser to the precondition
    ParserExtension.addNewPreCondition(decreases)
    // Add new parser to the invariants
    ParserExtension.addNewInvariantCondition(decreases)
    input
  }

  /** Called after methods are filtered but before the verification by the backend happens.
   *
   * @param input AST
   * @return Modified AST
   */
  override def beforeVerify(input: Program): Program = {
    // extract all decreases clauses from the program
    val newProgram = extractDecreasesClauses(input)

    if (deactivated){
      // if decreases checks are deactivated, only remove the decreases clauses from the program
      newProgram
    } else {
      val trafo = new Trafo(newProgram, reportError)

      val finalProgram = trafo.getTransformedProgram
      finalProgram
    }
  }


  /** Called after the verification. Error transformation should happen here.
   * This will only be called if verification took place.
   *
   * @param input Result of verification
   * @return Modified result
   */
  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    if (deactivated) return input // if decreases checks are deactivated no verification result mapping is required.

    input match {
      case Success => input
      case Failure(errors) => Failure(distinctErrors(errors.map({
        case a@AssertFailed(Assert(_), _, _) => a.transformedError()
        case e => e
      })))
    }
  }

  /**
   * Filters duplicates of errors.
   * Distinguished by Reason position and Reason
   * and Error Position and Error
   */
  private def distinctErrors(errors: Seq[AbstractError]): Seq[AbstractError] = {
    errors.groupBy(_.pos).flatMap(e => e._2.groupBy(optionReasonPosition).flatMap(e => e._2.distinct)).toSeq
  }

  private def optionReasonPosition(error: AbstractError): Option[Position] = {
    error match {
      case e: VerificationError => Some(e.reason.pos)
      case _ => None
    }
  }

  /** Can be called by the plugin to report an error while transforming the input.
   *
   * The reported error should correspond to the stage in which it is generated (e.g. no ParseError in beforeVerify)
   *
   * @param error The error to report
   */
  override def reportError(error: AbstractError): Unit = {
    super.reportError(error)
  }


  private def extractDecreasesClauses(program: Program): Program = {

    val result: Program = ViperStrategy.Slim({
      case f: Function =>
        val (pres, decreasesContainer) = extractDecreasesClauses(f.pres)

        val newFunction =
          if (pres != f.pres) {
            f.copy(pres = pres)(f.pos, f.info, f.errT)
          } else {
            f
          }

        decreasesContainer.appendToFunction(newFunction)
      case m: Method =>
        val (pres, decreasesContainer) = extractDecreasesClauses(m.pres)

        val newMethod =
          if (pres != m.pres) {
            m.copy(pres = pres)(m.pos, m.info, m.errT)
          } else {
            m
          }
        decreasesContainer.appendToMethod(newMethod)
      case w: While =>
        val (invs, decreasesContainer) = extractDecreasesClauses(w.invs)

        val newWhile =
          if (invs != w.invs) {
            w.copy(invs = invs)(w.pos, w.info, w.errT)
          } else {
            w
          }

        decreasesContainer.appendToWhile(newWhile)
    }).execute(program)
    result
  }

  /**
   * Extracts decreases clauses from the sequence of expression.
   * Only one of each decreases clause type are extracted.
   * If more exist, then consistency errors is issued.
   * @param exps: sequence of expression from which decreases clauses should be extracted.
   * @return exps without decreases clauses and a decreases container containing decreases clauses from exps.
   */
  private def extractDecreasesClauses(exps: Seq[Exp]): (Seq[Exp], DecreasesContainer) =
  {
    val (decreases, pres) = exps.partition(p => p.isInstanceOf[DecreasesExp])

    val tuples = decreases.collect{case p: DecreasesTuple => p}
    if (tuples.size > 1){
      reportError(ConsistencyError("Multiple decreases tuple.", tuples.head.pos))
    }
    val wildcards = decreases.collect{case p: DecreasesWildcard => p}
    if (wildcards.size > 1){
      reportError(ConsistencyError("Multiple decreases wildcard.", wildcards.head.pos))
    }
    val stars = decreases.collect{case p: DecreasesStar => p}
    if (stars.size > 1){
      reportError(ConsistencyError("Multiple decreases star.", stars.head.pos))
    }
    (pres, DecreasesContainer(tuples.headOption, wildcards.headOption, stars.headOption))
  }
}