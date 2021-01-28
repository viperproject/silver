// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.Program
import viper.silver.frontend._
import viper.silver.logger.ViperStdOutLogger
import viper.silver.reporter.StdIOReporter

class AstPositionsTests extends AnyFunSuite {
  object AstProvider extends ViperAstProvider(StdIOReporter(), ViperStdOutLogger("AstPositionsTestsLogger").get) {
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
    AstProvider.execute(Array("--ignoreFile", code_id))

    if (AstProvider.errors.isEmpty) {
      Some(AstProvider.translationResult)
    } else {
      AstProvider.logger.error(s"An error occurred while translating ${AstProvider.errors}")
      None
    }
  }

  test("Correct positions for methods in a parsed program") {
    import viper.silver.ast._

    val code =
      """field foo: Ref
        |method sum(g: Set[Ref])
        |  returns (res: Bool)
        |  ensures false
        |{
        |  inhale forall r: Ref :: r in g ==> acc(r.foo)
        |  var r1: Ref
        |  assume r1 in g
        |  inhale acc(r1.foo)
        |}
        |""".stripMargin

    val res: Program = generateViperAst(code).get
    res.methods.map(m => m.pos match {
      case spos: AbstractSourcePosition =>
        assert(spos.start !== spos.end.get)
      case _ =>
        fail("methods must have start and end positions set")
    })
  }
}
