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

class AstAnnotationTests extends AnyFunSuite {
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
    AstProvider.execute(Array("--ignoreFile", code_id))

    if (AstProvider.errors.isEmpty) {
      Some(AstProvider.translationResult)
    } else {
      AstProvider.logger.error(s"An error occurred while translating ${AstProvider.errors}")
      None
    }
  }

  test("Correct annotations for AST nodes in a parsed program") {
    import viper.silver.ast._

    val code =
      """@isghost("nope")
        |field f: Int
        |
        |@inlining("never", "inmylife")
        |function fun01(x: Ref, y: Ref, b: Bool): Int
        |  requires b ? acc(x.f) : acc(y.f)
        |
        |function fun02(x: Ref, y: Ref, b: Bool): Int
        |  requires acc(x.f, b ? write : none)
        |  requires acc(y.f, !b ? write : none)
        |
        |@inline("never", "ever")
        |@inline("ever")
        |predicate P(x: Ref)
        |
        |@interp("some smtlib thingy")
        |domain MyType {
        |
        |  @asd("test 123")
        |  @asdd("test 123", "test 125")
        |  function id(MyType): MyType
        |
        |  @asd("test 123")
        |  axiom {
        |    @asd("test 123", "huh")
        |    @asdasd()
        |    true
        |  }
        |}
        |
        |@setting("donotverify")
        |@verifier("none", "atall")
        |method m(x: Ref, y: Ref)
        |    requires acc(x.f)
        |    requires acc(y.f)
        |{
        |    var tmp: Int
        |    @annotatingastatement("the assignment", "12")
        |    @annotatingastatement("34")
        |    @suchannotations()
        |    tmp := @asd("test 123") fun02(x, @ann("this is ugly") y, true)
        |    y.f := 1
        |    assert tmp == fun02(x, y, true)
        |}
        |""".stripMargin

    val res: Program = generateViperAst(code).get

    val fieldAnn = res.findField("f").info.getUniqueInfo[AnnotationInfo].get
    assert(fieldAnn.values == Map("isghost" -> Seq("nope")))

    val predAnn = res.findPredicate("P").info.getUniqueInfo[AnnotationInfo].get
    assert(predAnn.values == Map("inline" -> Seq("never", "ever", "ever")))

    val dFuncAnn = res.findDomainFunction("id").info.getUniqueInfo[AnnotationInfo].get
    assert(dFuncAnn.values == Map("asd" -> Seq("test 123"), "asdd" -> Seq("test 123", "test 125")))

    val assignment = res.methods.head.body.get.ss(1)
    val assignmentAnn = assignment.info.getUniqueInfo[AnnotationInfo].get
    assert(assignmentAnn.values == Map("annotatingastatement" -> Seq("the assignment", "12", "34"), "suchannotations" -> Seq()))

    val rhs = assignment.asInstanceOf[LocalVarAssign].rhs
    val rhsAnn = rhs.info.getUniqueInfo[AnnotationInfo].get
    assert(rhsAnn.values == Map("asd" -> Seq("test 123")))

    val argAnn = rhs.asInstanceOf[FuncApp].args(1).info.getUniqueInfo[AnnotationInfo].get
    assert(argAnn.values == Map("ann" -> Seq("this is ugly")))
  }
}
