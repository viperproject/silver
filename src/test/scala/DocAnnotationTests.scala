// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.Program
import viper.silver.frontend._
import viper.silver.logger.ViperStdOutLogger
import viper.silver.reporter.StdIOReporter
import viper.silver.parser.{PProgram, PAnnotatedExp, PWhile}

class DocAnnotationTests extends AnyFunSuite {
  object AstProvider extends ViperAstProvider(StdIOReporter(), ViperStdOutLogger("DocAnnotationTestsLogger").get) {
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

  def generatePAstAndAst(code: String): Option[(PProgram, Program)] = {
    val code_id = code.hashCode.asInstanceOf[Short].toString
    AstProvider.setCode(code)
    AstProvider.execute(Seq("--ignoreFile", code_id))

    if (AstProvider.errors.isEmpty) {
      Some(AstProvider.parsingResult, AstProvider.translationResult)
    } else {
      AstProvider.logger.error(s"An error occurred while translating ${AstProvider.errors}")
      None
    }
  }

  test("Basic parsing of documentation") {
    import viper.silver.ast._

    val code =
      """/// a field
        |field f: Int
        |/// P is a predicate
        |predicate P(x: Int)
        |
        |/// a function
        |function fun(x: Int): Int {
        |  (x / 1 == x) ? 42 : 0
        |}
        |/// a second function
        |function fun2(x: Int): Int
        |    /// precondition
        |    requires x > 0
        |    /// post-
        |    /// condition
        |    ensures result > 0
        |
        |/// very important domain
        |domain ImportantType {
        |
        |  /// this function
        |  /// is crucial
        |  function phi(ImportantType): Int
        |
        |  /// the only axiom
        |  axiom {
        |    /// documenting an expression
        |    true
        |  }
        |}
        |
        |/// a macro
        |define plus(a, b) (a+b)
        |
        |/// this is a method
        |/// it does something
        |method m(x: Ref, y: Ref)
        |    /// this documents the first precondition
        |    requires acc(x.f)
        |    /// documentation of the second precondition
        |    requires acc(y.f)
        |{
        |    var local: Bool
        |
        |    while (true)///the invariant
        |      /// is always true
        |      invariant true
        |      /// termination
        |      decreases x.f
        |    {}
        |
        |}
        |""".stripMargin

    val pAst: PProgram = generatePAstAndAst(code).get._1

    val fieldAnn = pAst.fields.head.annotations.head.values.inner.first.get.str
    assert(fieldAnn == " a field")

    val predicateAnnotation = pAst.predicates.head.annotations.head.values.inner.first.get.str
    assert(predicateAnnotation == " P is a predicate")

    val functionAnnotation = pAst.functions.head.annotations.head.values.inner.first.get.str
    assert(functionAnnotation == " a function")

    val fun2Annotation = pAst.functions(1).annotations.head.values.inner.first.get.str
    val fun2PreAnnotations = pAst.functions(1).pres.head.annotations.map(_.values.inner.first.get.str)
    val fun2PostAnnotations = pAst.functions(1).posts.head.annotations.map(_.values.inner.first.get.str)
    assert(fun2Annotation == " a second function")
    assert(fun2PreAnnotations == Seq(" precondition"))
    assert(fun2PostAnnotations == Seq(" post-", " condition"))

    val domainAnnotation = pAst.domains.head.annotations.head.values.inner.first.get.str
    assert(domainAnnotation == " very important domain")

    val domainFunctionAnnotations = pAst.domains.head.members.inner.funcs.head.annotations.map(_.values.inner.first.get.str)
    assert(domainFunctionAnnotations == Seq(" this function", " is crucial"))

    val axiomAnnotations = pAst.domains.head.members.inner.axioms.head.annotations.map(_.values.inner.first.get.str)
    assert(axiomAnnotations == Seq(" the only axiom"))
    val axiomExpAnnotations = pAst.domains.head.members.inner.axioms.head.exp.e.inner.asInstanceOf[PAnnotatedExp].annotation.values.inner.first.get.str
    assert(axiomExpAnnotations == " documenting an expression")

    val macroAnnotation = pAst.macros.head.annotations.head.values.inner.first.get.str
    assert(macroAnnotation == " a macro")

    val methodAnnotations = pAst.methods.head.annotations.map(_.values.inner.first.get.str)
    assert(methodAnnotations == Seq(" this is a method", " it does something"))

    val methodPreAnnotations = pAst.methods.head.pres.toSeq.map(_.annotations.head.values.inner.first.get.str)
    assert(methodPreAnnotations == Seq(" this documents the first precondition", " documentation of the second precondition"))

    val loopInvariantAnnotations = pAst.methods.head.body.get.ss.inner.inner.collect {
          case (_, w: PWhile) => w.invs.toSeq.flatMap(_.annotations.map(_.values.inner.first.get.str))
    }.flatten
    assert(loopInvariantAnnotations == Seq("the invariant", " is always true", " termination"))
  }
}