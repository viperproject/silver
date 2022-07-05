// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import TestHelpers.MockSilFrontend
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter

import java.io.{File, FileWriter}

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

  def tt = TrueLit()()
  def and(t: Exp, u: Exp) = And(t, u)()
  def or(t: Exp, u: Exp) = Or(t, u)()

  test("Parsing a pretty-printed 'And' expression should return the same expression") {
    compareToParsed(and(and(tt, tt), tt))
  }

  test("Parsing a pretty-printed 'Or' expression should return the same expression") {
    compareToParsed(or(or(tt, tt), tt))
  }

  test("Parsing pretty-printed '-5' should return the same expression") {
    compareToParsed(IntLit(-5)())
  }

  private def compareToParsed(exp: Exp): Unit = {
    val declStmt = LocalVarDeclStmt(LocalVarDecl("tmp", exp.typ)())()
    val assign = LocalVarAssign(declStmt.decl.localVar, exp)()
    compareToParsed(
      Program(
        Nil,
        Nil,
        Nil,
        Nil,
        List(
          Method(
            "test",
            Nil,
            Nil,
            Nil,
            Nil,
            Some(
              Seqn(
                List(declStmt, assign),
                  Nil
                )()
              )
            )()
        ),
        Nil
      )()
    )
  }

  private def compareToParsed(prog: Program): Unit = {
    val frontend = new MockSilFrontend
    val printed = FastPrettyPrinter.pretty(prog)
    val file = File.createTempFile("parsetest", ".vpr")
    val fw = new FileWriter(file)
    fw.write(printed)
    fw.close()

    def getExp(program: Program) = {
      program.methods.head.body.get.ss(1)
    }

    frontend.translate(file.toPath) match {
      case (Some(result), _) =>
        assert(getExp(result) == getExp(prog), s"${prog} did not match ${result}")
      case (None, errors) =>
        sys.error("Error occurred during translating: " + errors)
    }
  }
}
