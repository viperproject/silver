/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */
package viper.silicon.tests

import org.scalatest.FunSuite
import viper.silver.verifier.ConsistencyError
import viper.silver.ast._
import org.scalatest.Matchers


class ConsistencyTests extends FunSuite with Matchers {

    /* These tests invoke errors from consistency checks made at AST nodes.
    At the moment, many of these errors cannot be invoked by parsing a Silver program
    because the corresponding checks are also made at the type-checking stage, and thus
    the final AST is never created. It is desirable to remove these duplicate checks from
    the type-checker at some point.
   */

  test("While loop condition"){
    val loop : While = While(IntLit(1)(NoPosition, NoInfo, NoTrafos), Seq(),
      Seqn(Seq(), Seq())(NoPosition, NoInfo, NoTrafos))(NoPosition, NoInfo, NoTrafos)
    loop.checkTransitively should be (Seq(
      ConsistencyError("While loop condition must be of type Bool, but found Int", NoPosition)))
  }

  test("Identifier checks"){
    val funcapp1 : FuncApp = FuncApp("f1", Seq())(NoPosition, NoInfo, Int, Seq(), NoTrafos)
    val methodcall1: MethodCall = MethodCall("m2", Seq(), Seq())(NoPosition, NoInfo, NoTrafos)
    val method1 : Method = Method("m1", Seq(), Seq(), Seq(), Seq(),
      Seqn(Seq[Stmt](LocalVarAssign(LocalVar("i")(Int, NoPosition, NoInfo, NoTrafos), funcapp1)(NoPosition, NoInfo,
        NoTrafos), Goto("lbl1")(NoPosition, NoInfo, NoTrafos), methodcall1), Seq())(NoPosition, NoInfo, NoTrafos))(NoPosition, NoInfo, NoTrafos)
    val prog : Program = Program(Seq(), Seq(Field("j", Int)(NoPosition, NoInfo, NoTrafos), Field("j", Bool)(NoPosition, NoInfo, NoTrafos)),
      Seq(), Seq(), Seq(method1))(NoPosition, NoInfo, NoTrafos)

    prog.checkTransitively should be (Seq(
      ConsistencyError("Duplicate identifier j found.", NoPosition),
      ConsistencyError("Local variable i not found.", NoPosition),
      ConsistencyError("No matching identifier f1 found of type Function.", NoPosition),
      ConsistencyError("No matching identifier lbl1 found of type Label.", NoPosition),
      ConsistencyError("No matching identifier m2 found of type Method.", NoPosition)))
  }

  test("Conditional expression"){
    val condexp1 : CondExp = CondExp(BoolLit(true)(NoPosition, NoInfo, NoTrafos),
      IntLit(5)(NoPosition, NoInfo, NoTrafos), FuncApp("f1", Seq())(NoPosition, NoInfo, Bool, Seq(), NoTrafos))(NoPosition, NoInfo, NoTrafos)

    condexp1.checkTransitively should be (Seq(
      ConsistencyError("Second and third parameter types of conditional expression must match, but found Int and Bool", NoPosition)
    ))
  }

  test("Field assignment"){
    val fieldassign1 : FieldAssign = FieldAssign(FieldAccess(IntLit(5)(NoPosition, NoInfo, NoTrafos),
      Field("i", Int)(NoPosition, NoInfo, NoTrafos))(NoPosition, NoInfo, NoTrafos),
      BoolLit(false)(NoPosition, NoInfo, NoTrafos))(NoPosition, NoInfo, NoTrafos)

    fieldassign1.checkTransitively should be (Seq(
      ConsistencyError("Right-hand side false is not assignable to left-hand side 5.i.", NoPosition)))
  }
}