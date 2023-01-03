// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.refute

import fastparse.P
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast._
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser.FastParser
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.reporter.Entity
import viper.silver.verifier._
import viper.silver.verifier.errors.AssertFailed

import scala.annotation.unused

class RefutePlugin(@unused reporter: viper.silver.reporter.Reporter,
                   @unused logger: ch.qos.logback.classic.Logger,
                   @unused config: viper.silver.frontend.SilFrontendConfig,
                   fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{FP, keyword, exp, ParserExtension}

  /** Keyword used to define refute statements. */
  private val refuteKeyword: String = "refute"

  private var refuteAsserts: Map[Position, Refute] = Map()
  private var refuteAssertsPerEntity: Map[(Method, Position), Refute] = Map()

  /** Parser for refute statements. */
  def refute[_: P]: P[PRefute] =
    FP(keyword(refuteKeyword) ~/ exp).map{ case (pos, e) => PRefute(e)(pos) }

  /** Add refute to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String](refuteKeyword))
    // Add new parser to the precondition
    ParserExtension.addNewStmtAtEnd(refute(_))
    input
  }

  /**
   * Remove refute statements from the AST and add them as non-det asserts.
   * The ⭐ is nice since such a variable name cannot be parsed, but will it cause issues?
   */
  override def beforeVerify(input: Program): Program = {
    val transformedMethods = input.methods.map(method =>
      ViperStrategy.Slim({
        case r@Refute(exp) =>
          this.refuteAsserts += (r.pos -> r)
          this.refuteAssertsPerEntity += ((method, r.pos) -> r)
          val refutesInMethod = this.refuteAssertsPerEntity.count {
            case ((m, _), _) => method == m
          }
          val nonDetLocalVarDecl = LocalVarDecl(s"__plugin_refute_nondet$refutesInMethod", Bool)(r.pos)
          Seqn(Seq(
            If(nonDetLocalVarDecl.localVar,
              Seqn(Seq(
                Assert(exp)(r.pos, RefuteInfo),
                Inhale(BoolLit(false)(r.pos))(r.pos)
              ), Seq())(r.pos),
              Seqn(Seq(), Seq())(r.pos))(r.pos)
          ),
            Seq(nonDetLocalVarDecl)
          )(r.pos)
      }).recurseFunc({
        case Method(_, _, _, _, _, body) => Seq(body)
      }).execute[Method](method))
    Program(input.domains, input.fields, input.functions, input.predicates, transformedMethods, input.extensions)(input.pos, input.info, input.errT)
  }

  /** Remove refutation related errors for the current entity and add refuteAsserts in this entity that didn't report an error. */
  override def mapEntityVerificationResult(entity: Entity, input: VerificationResult): VerificationResult = {
    val occurredNonRefuteErrors = input match {
      case Success => Seq()
      case Failure(errors) =>
        errors.filter {
          case AssertFailed(a, _, _) if a.info == RefuteInfo =>
            // remove entries whose method and position match:
            this.refuteAssertsPerEntity = this.refuteAssertsPerEntity.filter {
              case ((m, pos), _) if entity == m && a.pos == pos => false
              case _ => true
            }
            false
          case _ => true
        }
    }
    val missingErrorsInEntity = this.refuteAssertsPerEntity.flatMap {
      case ((m, _), refute) if entity == m => Some(RefuteFailed(refute, RefutationTrue(refute.exp)))
      case _ => None
    }
    val errors = occurredNonRefuteErrors ++ missingErrorsInEntity
    if (errors.isEmpty) Success
    else Failure(errors)
  }

  /** Remove refutation related errors (for all entities) and add refuteAsserts (for all entities) that didn't report an error. */
  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    val occurredNonRefuteErrors = input match {
      case Success => Seq()
      case Failure(errors) =>
        errors.filter {
          case AssertFailed(a, _, _) if a.info == RefuteInfo =>
            this.refuteAsserts -= a.pos
            false
          case _ => true
        }
    }
    val missingErrorsInEntity = this.refuteAsserts.map {
      case (_, refute) => RefuteFailed(refute, RefutationTrue(refute.exp))
    }
    val errors = occurredNonRefuteErrors ++ missingErrorsInEntity
    if (errors.isEmpty) Success
    else Failure(errors)
  }
}
