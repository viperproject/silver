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
    // Check position of field
    assert(res.fields.length === 1)
    res.fields(0).pos match {
      case spos: AbstractSourcePosition =>
        assert(spos.start.line === 1 && spos.end.get.line === 1)
        // Here it is unclear if we want to include the `field ` part in the pos
        assert(spos.start.column === 1 || spos.start.column === 7)
        assert( spos.end.get.column === 15)
      case _ =>
        fail("fields must have start and end positions set")
    }
    // Check position of method
    assert(res.methods.length === 1)
    val m: Method = res.methods(0)
    m.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 2 && spos.end.get.line === 10)
        assert(spos.start.column === 1 && spos.end.get.column === 2)
      }
      case _ =>
        fail("methods must have start and end positions set")
    }
    // Check position of method arg
    assert(m.formalArgs.length === 1)
    val fa: LocalVarDecl = m.formalArgs(0)
    fa.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 2 && spos.end.get.line === 2)
        assert(spos.start.column === 12 && spos.end.get.column === 13)
      }
      case _ =>
        fail("method args must have start and end positions set")
    }
    // Check position of method post
    assert(m.posts.length === 1)
    val post: Exp = m.posts(0)
    post.pos match {
      case spos: AbstractSourcePosition => {
        assert(spos.start.line === 4 && spos.end.get.line === 4)
        assert(spos.start.column === 11 && spos.end.get.column === 16)
      }
      case _ =>
        fail("method posts must have start and end positions set")
    }
    // Check position of body
    if (m.body.get.ss.length == 1) {
      val block: Stmt = m.body.get.ss(0)
      block.pos match {
        case spos: AbstractSourcePosition => {
          assert(spos.start.line === 5 && spos.end.get.line === 10)
          assert(spos.start.column === 1 && spos.end.get.column === 2)
        }
        case _ =>
          fail("statements must have start and end positions set")
      }
      if (block.isInstanceOf[Seqn]) {
        // Check position of forall
        assert(block.asInstanceOf[Seqn].ss.length === 4)
        val forall: Stmt = block.asInstanceOf[Seqn].ss(0)
        forall.pos match {
          case spos: AbstractSourcePosition => {
            assert(spos.start.line === 6 && spos.end.get.line === 6)
            assert(spos.start.column === 3 && spos.end.get.column === 48)
          }
          case _ =>
            fail("forall must have start and end positions set")
        }
      } else {
        fail("Failed to check position of statements in method body due to layout change")
      }
    } else {
      fail("Failed to check position of statements in method body due to layout change")
    }
  }
}
