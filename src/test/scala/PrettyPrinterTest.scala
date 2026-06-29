// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter
import viper.silver.frontend.{DefaultStates, ViperAstProvider}
import viper.silver.logger.ViperStdOutLogger
import viper.silver.reporter.StdIOReporter

class PrettyPrinterTest extends AnyFunSuite with Matchers {
  test("The comment of nested Seqn-s is printed correctly") {
    val comment = "Comment XYZ"
    val a = Seqn(Seq(), Seq())(NoPosition, SimpleInfo(Seq(comment)))
    val b = Seqn(Seq(a), Seq())(NoPosition, NoInfo)
    val c = Seqn(Seq(b), Seq())(NoPosition, NoInfo)

    val printed = FastPrettyPrinter.pretty(c)

    // In particular, we don't want `printed` to end with a newline.
    assert(printed == "// " + comment)
  }

  object AstProvider extends ViperAstProvider(StdIOReporter(), ViperStdOutLogger("AstAnnotationTestsLogger").get) {
    def setCode(code: String): Unit = {
      _input = Some(code)
    }

    override def reset(input: java.nio.file.Path): Unit = {
      if (state < DefaultStates.Initialized) sys.error("The translator has not been initialized.")
      _state = DefaultStates.InputSet
      _inputFile = Some(input)

      /** must be set by [[setCode]] */
      // _input = None
      _errors = Seq()
      _parsingResult = None
      _semanticAnalysisResult = None
      _verificationResult = None
      _program = None
      resetMessages()
    }
  }

  def generateViperAst(code: String): Option[Program] = {

    val code_id = code.hashCode.asInstanceOf[Short].toString
    AstProvider.setCode(code)
    AstProvider.execute(Seq("--ignoreFile", code_id))

    if (AstProvider.errors.isEmpty) {
      Some(AstProvider.translationResult)
    } else {
      AstProvider.logger.error(s"An error occurred while translating ${AstProvider.errors}")
      None
    }
  }

  test("Pretty printer and parser roundtrip yields same result") {
    import viper.silver.ast._

    val code =
      """
        |domain Measures {  // used for issue 154 test, see below
        |  function Measure$contains(Ref, Int): Bool
        |  function Measure$value(slf: Ref, k: Int): Int
        |}
        |
        |function issue154(self: Ref, key: Int, value: Int): Bool
        |  ensures result == (Measure$contains(self, key) ==> (Measure$value(self, key) > value))
        |
        |function concatFirst(xs: Seq[Int], ys: Seq[Int]): Int {
        |    (xs ++ ys)[0]  // issue #496
        |}
        |
        |method bodyless()  // bodyless method, issue #223
        |
        |// scopes, issue #697
        |method test() {
        |    {
        |        var index: Int
        |        index := index + 1
        |        index := index + 2
        |        var p: Int
        |        p := 1 / 2  // integer division
        |    }
        |    {
        |        var index: Int
        |        if (index > 5) {
        |           index := 56
        |        } elseif (index < -56) {
        |           var index2: Ref
        |           index := 77
        |        } else {
        |           index := 45
        |           while (index != 0)
        |             invariant index > 23
        |           {
        |              var index2: Ref
        |              index2 := null
        |              var m: Map[Bool, Bool]
        |              m := Map(true := false, false := true)  // maps, issue #619
        |           }
        |        }
        |    }
        |}
        |""".stripMargin

    val origProgram: Program = generateViperAst(code).get
    // Pretty print and reparse
    val res = generateViperAst(origProgram.toString()).get
    val origString = origProgram.toString()
    val resString = res.toString()
    assert(origString == resString)
  }

  test("Test pretty printing conditional wildcard termination measures") {
    import viper.silver.plugin.standard.termination.DecreasesWildcard

    val m = Method(
      name = "f",
      formalArgs = Seq.empty,
      formalReturns = Seq.empty,
      pres = Seq(DecreasesWildcard(Some(TrueLit()()))()),
      posts = Seq.empty,
      body = None
    )()
    val actual = m.toString().trim
    val expected =
      """
        |method f()
        |  decreases _ if true
        |""".stripMargin.trim
    assert(actual == expected)
  }

  test("Test pretty printing conditional tuple termination measures") {
    import viper.silver.plugin.standard.termination.DecreasesTuple

    val m = Method(
      name = "f",
      formalArgs = Seq.empty,
      formalReturns = Seq.empty,
      pres = Seq(DecreasesTuple(Seq(IntLit(1)()), Some(TrueLit()()))()),
      posts = Seq.empty,
      body = None
    )()
    val actual = m.toString().trim
    val expected =
      """
        |method f()
        |  decreases 1 if true
        |""".stripMargin.trim
    assert(actual == expected)
  }


}
