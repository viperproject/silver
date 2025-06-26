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
    AstProvider.execute(Seq("--ignoreFile", code_id))

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
      """field foo: Int
        |method sum(x: Ref, g: Set[Ref])
        |  returns (res: Bool)
        |  ensures false && 4/x.foo > 0
        |  ensures 3 < 4 < 5
        |{
        |  inhale forall r: Ref :: r in g ==> acc(r.foo)
        |  assert acc(x.foo)
        |  var r1: Ref
        |  assume r1 in g
        |}
        |method bar(r: Ref)
        |  requires  0  >  r . foo
        |// Comment
        |function end(): Ref""".stripMargin

    val res: Program = generateViperAst(code).get
    // Check position of field
    assert(res.fields.length === 1)
    val f: Field = res.fields(0)
    f.pos match {
      case spos: AbstractSourcePosition =>
        assert(spos.start.line === 1 && spos.end.get.line === 1)
        // Here it is unclear if we want to include the `field ` part in the pos
        assert(spos.start.column === 1 || spos.start.column === 7)
        assert( spos.end.get.column === 15)
      case _ =>
        fail("fields must have start and end positions set")
    }
    // Check position of method
    assert(res.methods.length === 2)
    val m: Method = res.methods(0)
    m.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 2 && spos.end.get.line === 11)
        assert(spos.start.column === 1 && spos.end.get.column === 2)
      }
      case _ =>
        fail("methods must have start and end positions set")
    }
    // Check position of method arg
    assert(m.formalArgs.length === 2)
    val fa: LocalVarDecl = m.formalArgs(0)
    fa.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 2 && spos.end.get.line === 2)
        assert(spos.start.column === 12 && spos.end.get.column === 13)
      }
      case _ =>
        fail("method args must have start and end positions set")
    }
    // Check positions of method posts
    assert(m.posts.length === 2)
    val post1: Exp = m.posts(0).asInstanceOf[BinExp].args(1);
    post1.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 4 && spos.end.get.line === 4)
        assert(spos.start.column === 20 && spos.end.get.column === 31)
      }
      case _ =>
        fail("method posts must have start and end positions set")
    }
    val post2: BinExp = m.posts(1).asInstanceOf[BinExp]
    post2.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 5 && spos.end.get.line === 5)
        assert(spos.start.column === 11 && spos.end.get.column === 20)
      }
      case _ =>
        fail("method posts must have start and end positions set")
    }
    post2.left.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 5 && spos.end.get.line === 5)
        assert(spos.start.column === 11 && spos.end.get.column === 16)
      }
      case _ =>
        fail("method posts must have start and end positions set")
    }
    post2.right.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 5 && spos.end.get.line === 5)
        assert(spos.start.column === 15 && spos.end.get.column === 20)
      }
      case _ =>
        fail("method posts must have start and end positions set")
    }
    // Check position of body
    val block = m.body.get
    block.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 6 && spos.end.get.line === 11)
        assert(spos.start.column === 1 && spos.end.get.column === 2)
      }
      case _ =>
        fail("statements must have start and end positions set")
    }
    // Check position of forall
    assert(block.ss.length === 4)
    val forall: Stmt = block.ss(0)
    forall.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 7 && spos.end.get.line === 7)
        assert(spos.start.column === 3 && spos.end.get.column === 48)
      }
      case _ =>
        fail("forall must have start and end positions set")
    };
    // Check position of assert
    val assert_exp: Exp = block.ss(1).asInstanceOf[Assert].exp
    assert_exp.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 8 && spos.end.get.line === 8)
        assert(spos.start.column === 10 && spos.end.get.column === 20)
      }
      case _ =>
        fail("forall must have start and end positions set")
    }

    // Check position of second method
    val m2: Method = res.methods(1);
    m2.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 12 && spos.end.get.line === 13)
        assert(spos.start.column === 1 && spos.end.get.column === 26)
      }
      case _ =>
        fail("methods must have start and end positions set")
    }
    // Check position of second method precond
    val pre: Exp = m2.pres(0);
    pre.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 13 && spos.end.get.line === 13)
        assert(spos.start.column === 13 && spos.end.get.column === 26)
      }
      case _ =>
        fail("methods must have start and end positions set")
    }
    // Check position of function
    assert(res.functions.length === 1)
    val fn: Function = res.functions(0)
    fn.pos match {
      case spos: AbstractSourcePosition =>
        assert(spos.start.line === 15 && spos.end.get.line === 15)
        // Here it is unclear if we want to include the `function ` part in the pos
        assert(spos.start.column === 1 || spos.start.column === 10)
        assert(spos.end.get.column === 20)
      case _ =>
        fail("functions must have start and end positions set")
    }
  }
}
