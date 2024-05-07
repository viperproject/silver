// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.refute

import fastparse._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast._
import viper.silver.parser.FastParserCompanion
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

  import fp.{exp, ParserExtension, lineCol, _file}
  import FastParserCompanion.{PositionParsing, reservedKw, whitespace}

  /** Parser for refute statements. */
  def refute[$: P]: P[PRefute] = P((P(PRefuteKeyword) ~ exp) map (PRefute.apply _).tupled).pos

  /** Add refute to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set(PRefuteKeyword))
    // Add new parser to the precondition
    ParserExtension.addNewStmtAtEnd(refute(_))
    input
  }

  /**
   * Remove refute statements from the AST and add them as non-det asserts.
   */
  override def beforeVerify(input: Program): Program = {
    val transformedMethods = input.methods.map(method => {
      var refutesInMethod = 0
      ViperStrategy.Slim({
        case r@Refute(exp) =>
          refutesInMethod += 1
          val nonDetLocalVarDecl = LocalVarDecl(s"__plugin_refute_nondet$refutesInMethod", Bool)(r.pos)
          Seqn(Seq(
            If(nonDetLocalVarDecl.localVar,
              Seqn(Seq(
                Assert(exp)(r.pos, RefuteInfo(r)),
                Inhale(BoolLit(false)(r.pos))(r.pos, Synthesized)
              ), Seq())(r.pos),
              Seqn(Seq(), Seq())(r.pos))(r.pos)
          ),
            Seq(nonDetLocalVarDecl)
          )(r.pos)
      }).recurseFunc({
        case method: Method => Seq(method.body)
      }).execute[Method](method)
    })
    Program(input.domains, input.fields, input.functions, input.predicates, transformedMethods, input.extensions)(input.pos, input.info, input.errT)
  }

  /** Remove refutation related errors for the current entity and add refuteAsserts in this entity that didn't report an error. */
  override def mapEntityVerificationResult(entity: Entity, input: VerificationResult): VerificationResult =
    mapVerificationResultsForNode(entity, input)

  /** Remove refutation related errors (for all entities) and add refuteAsserts (for all entities) that didn't report an error. */
  override def mapVerificationResult(program: Program, input: VerificationResult): VerificationResult =
    mapVerificationResultsForNode(program, input)

  private def mapVerificationResultsForNode(n: Node, input: VerificationResult): VerificationResult = {
    val (refutesForWhichErrorOccurred, otherErrors) = input match {
      case Success => (Seq.empty, Seq.empty)
      case Failure(errors) => errors.partitionMap {
        case AssertFailed(NodeWithRefuteInfo(RefuteInfo(r)), _, _) => Left((r, r.pos))
        case err => Right(err)
      }
    }
    val refutesContainedInNode = n.collect {
      case NodeWithRefuteInfo(RefuteInfo(r)) => (r, r.pos)
    }
    // note that we include positional information in `refutesForWhichErrorOccurred` and `refutesContainedInNode` such
    // that we do not miss errors just because the same refute statement occurs multiple times
    val refutesForWhichNoErrorOccurred = refutesContainedInNode.filterNot(refutesForWhichErrorOccurred.contains(_))
    val missingErrorsInNode = refutesForWhichNoErrorOccurred.map{
      case (refute, _) => RefuteFailed(refute, RefutationTrue(refute.exp))
    }

    val errors = otherErrors ++ missingErrorsInNode
    if (errors.isEmpty) Success
    else Failure(errors)
  }
}

object NodeWithRefuteInfo {
  def unapply(node : Node) : Option[RefuteInfo] = node match {
    case i: Infoed => i.info.getUniqueInfo[RefuteInfo]
    case _ => None
  }
}
