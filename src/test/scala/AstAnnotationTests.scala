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
        |function fun02(x: Ref, y: Ref, b: Bool, i: Int): Int
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
        |    @such.annotations()
        |    tmp := @asd("test 123") fun02(x, @ann("this is ugly") y, true, @ann() ((@ann2() tmp) + tmp))
        |    y.f := 1
        |    assert tmp == fun02(x, y, true, 0)
        |}
        |""".stripMargin

    val origProgram: Program = generateViperAst(code).get
    // Pretty print and reparse to make sure annotations are preserved correctly.
    val res = generateViperAst(origProgram.toString()).get

    val fieldAnn = res.findField("f").info.getUniqueInfo[AnnotationInfo].get
    assert(fieldAnn.values == Map("isghost" -> Seq("nope")))

    val predAnn = res.findPredicate("P").info.getUniqueInfo[AnnotationInfo].get
    assert(predAnn.values == Map("inline" -> Seq("never", "ever", "ever")))

    val dFuncAnn = res.findDomainFunction("id").info.getUniqueInfo[AnnotationInfo].get
    assert(dFuncAnn.values == Map("asd" -> Seq("test 123"), "asdd" -> Seq("test 123", "test 125")))

    val assignment = res.methods.head.body.get.ss(1)
    val assignmentAnn = assignment.info.getUniqueInfo[AnnotationInfo].get
    assert(assignmentAnn.values == Map("annotatingastatement" -> Seq("the assignment", "12", "34"), "such.annotations" -> Seq()))

    val lhs = assignment.asInstanceOf[LocalVarAssign].lhs
    val lhsAnn = lhs.info.getUniqueInfo[AnnotationInfo]
    assert(lhsAnn.isEmpty || lhsAnn.get.values.isEmpty)

    val rhs = assignment.asInstanceOf[LocalVarAssign].rhs
    val rhsAnn = rhs.info.getUniqueInfo[AnnotationInfo].get
    assert(rhsAnn.values == Map("asd" -> Seq("test 123")))

    val argAnn = rhs.asInstanceOf[FuncApp].args(1).info.getUniqueInfo[AnnotationInfo].get
    assert(argAnn.values == Map("ann" -> Seq("this is ugly")))

    val lastArg = rhs.asInstanceOf[FuncApp].args(3)
    val lastArgAnn = lastArg.info.getUniqueInfo[AnnotationInfo].get
    assert(lastArgAnn.values == Map("ann" -> Seq()))

    val lastArgLeft = lastArg.asInstanceOf[Add].left
    val lastArgLeftAnn = lastArgLeft.info.getUniqueInfo[AnnotationInfo].get
    assert(lastArgLeftAnn.values == Map("ann2" -> Seq()))

    val lastArgRight = lastArg.asInstanceOf[Add].right
    val lastArgRightAnn = lastArgRight.info.getUniqueInfo[AnnotationInfo]
    assert(lastArgRightAnn.isEmpty || lastArgRightAnn.get.values == Map())
  }
}
