// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silver.testing

import fastparse._
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser.{FastParser, PAccPred, PBinExp, PExp, PSymOp}

import java.nio.file.Path

trait CounterexampleVariablesTests extends SilSuite {
  override val testDirectories: Seq[String] = Seq("counterexample_variables")

  override def buildTestInput(file: Path, prefix: String): DefaultAnnotatedTestInput =
    CounterexampleTestInput(file, prefix)

  def createExpectedValuesCounterexampleAnnotation(id: OutputAnnotationId, file: Path, forLineNr: Int, expectedCounterexample: ExpectedCounterexample): CustomAnnotation

  /** we override the default annotation parser because we use special annotations to express expected counterexamples */
  object CounterexampleTestInput extends TestAnnotationParser {
    /**
      * Creates an annotated test input by parsing all annotations in the files
      * that belong to the given test input.
      */
    def apply(i: TestInput): DefaultAnnotatedTestInput =
      DefaultAnnotatedTestInput(i.name, i.prefix, i.files, i.tags,
        parseAnnotations(i.files))

    def apply(file: Path, prefix: String): DefaultAnnotatedTestInput =
      apply(DefaultTestInput(file, prefix))

    override def getAnnotationFinders: Seq[(String, Path, Int) => Option[TestAnnotation]] = {
      super.getAnnotationFinders :+ isExpectedCounterexample
    }

    // the use of comma is excluded from value ID (i.e. after the colon) to avoid ambiguities with the model
    // note that the second capturing group could be turned into a non-capturing group but this would break compatibility
    // with the parent trait
    override val outputIdPattern: String = "([^:]*)(:([^,]*))?"

    private def isExpectedCounterexample(annotation: String, file: Path, lineNr: Int): Option[TestAnnotation] = {
      def parseExpectedCounterexample(id: OutputAnnotationId, expectedCounterexampleString: String): Option[CustomAnnotation] = {
        // in order to reuse as much of the existing Viper parser as possible, we have to initialize the `_file` and `_line_offset` fields:
        val fp = new FastParser()
        fp._file = file.toAbsolutePath
        val lines = expectedCounterexampleString.linesWithSeparators
        fp._line_offset = (lines.map(_.length) ++ Seq(0)).toArray
        var offset = 0
        for (i <- fp._line_offset.indices) {
          val line_length = fp._line_offset(i)
          fp._line_offset(i) = offset
          offset += line_length
        }
        val cParser = new CounterexampleParser(fp)
        // now parsing is actually possible:
        fastparse.parse(expectedCounterexampleString, cParser.expectedCounterexample(_)) match {
          case Parsed.Success(expectedCounterexample, _) => Some(createExpectedValuesCounterexampleAnnotation(id, file, lineNr, expectedCounterexample))
          case Parsed.Failure(_, _, extra) =>
            println(s"Parsing expected counterexample failed in file $file: ${extra.trace().longAggregateMsg}")
            None
        }
      }

      val regex = ("""^ExpectedCounterexample\(""" + outputIdPattern + """, (.*)\)$""").r
      annotation match {
        case regex(keyId, _, null, counterexample) =>
          parseExpectedCounterexample(OutputAnnotationId(keyId, None), counterexample)
        case regex(keyId, _, valueId, counterexample) =>
          parseExpectedCounterexample(OutputAnnotationId(keyId, Some(valueId)), counterexample)
        case _ => None
      }
    }
  }
}

/**
  * Simple input language to describe an expected counterexample with corresponding parser.
  * Currently, a counterexample is expressed by a comma separated list of access predicates and equalities (using the
  * same syntax as in Viper)
  */
class CounterexampleParser(fp: FastParser) {
  import fp.{accessPred, eqExp}

  def expectedCounterexample[_: P]: P[ExpectedCounterexample] =
    (Start ~ "(" ~ (accessPred | eqExp).rep(0, ",") ~ ")" ~ End)
      .map(ExpectedCounterexample)
}

case class ExpectedCounterexample(exprs: Seq[PExp]) {
  assert(exprs.forall {
    case _: PAccPred => true
    case PBinExp(_, r, _) if r.rs == PSymOp.EqEq => true
    case _ => false
  })
}