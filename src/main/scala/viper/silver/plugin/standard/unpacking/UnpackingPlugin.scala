// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.unpacking

import fastparse._
import viper.silver.ast._
import viper.silver.parser.{FastParser, FastParserCompanion, PAnnotatedStmt, PCall, PProgram, PStmt}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.reporter.Entity
import viper.silver.verifier._

import scala.annotation.unused
import scala.collection.mutable

class UnpackingPlugin(@unused reporter: viper.silver.reporter.Reporter,
                      @unused logger: ch.qos.logback.classic.Logger,
                      @unused config: viper.silver.frontend.SilFrontendConfig,
                      fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{exp, ParserExtension, lineCol, _file}
  import FastParserCompanion.{PositionParsing, reservedKw, whitespace}

  private val labels: mutable.Map[String, String] = mutable.Map()

  /** Parser for unpack statements. */
  def unpack[$: P]: P[PUnpack] = P((P(PUnpackKeyword) ~ exp) map (PUnpack.apply _).tupled).pos

  /** Add unpack to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set(PUnpackKeyword))
    // Add new parser to the precondition
    ParserExtension.addNewStmtAtEnd(unpack(_))
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    PProgram(input.imported, input.members)(input.pos, input.localErrors, input.offsets, input.rawProgram)
  }

  /**
   *
   */
  override def beforeVerify(input: Program): Program = {
    val transformedMethods = input.methods.map(method => {
      if (method.body.isDefined) {
        method.body.get.ss.foreach(stmt => {
          case c@MethodCall(name, _, _) =>
            val info = c.info.getUniqueInfo[AnnotationInfo]
            if (info.isDefined && info.asInstanceOf[AnnotationInfo].values.head._1.equals("collectPredicates")) {
              println("Here")
              labels += (info.asInstanceOf[AnnotationInfo].values.head._2[0] -> name)
            }
          case _ =>
        })
      }
    })

    println(labels)

    Program(input.domains, input.fields, input.functions, input.predicates, input.methods, input.extensions)(input.pos, input.info, input.errT)
  }

  /** Remove refutation related errors for the current entity and add refuteAsserts in this entity that didn't report an error. */
  override def mapEntityVerificationResult(entity: Entity, input: VerificationResult): VerificationResult =
    mapVerificationResultsForNode(entity, input)

  /** Remove refutation related errors (for all entities) and add refuteAsserts (for all entities) that didn't report an error. */
  override def mapVerificationResult(program: Program, input: VerificationResult): VerificationResult =
    mapVerificationResultsForNode(program, input)

  private def mapVerificationResultsForNode(n: Node, input: VerificationResult): VerificationResult = {
    input
  }
}

