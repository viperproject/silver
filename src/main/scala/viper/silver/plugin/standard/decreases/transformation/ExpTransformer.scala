// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.decreases.transformation

import viper.silver.ast._
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.verifier.ConsistencyError

/**
  * A basic interface which helps to rewrite an expression (e.g. a function body) into a stmt (e.g. for a method body).
  * Some basic transformations are already implemented.
  * If no transformation is defined for an expression a consistency error is reported (to avoid unsound results).
  */
trait ExpTransformer extends ErrorReporter {

  /**
    * Transforms an expression into a statement.
    * If an unsupported expression is detected, i.e. an expression for which no transformation is defined,
    * a consistency error is reported (to avoid unsound results).
    * Parts of the expressions which stay expressions (e.g. the condition in a if clause)
    * are also transformed into statements and prepended to the other statement.
    * @return a statement representing the expression
    */
  def transformExp: PartialFunction[(Exp, ExpressionContext), Stmt] = {
    case (CondExp(cond, thn, els), c) =>
      val condStmt = transformExp(cond, c)
      val thnStmt = transformExp(thn, c)
      val elsStmt = transformExp(els, c)

      val ifStmt = if (!(thnStmt == EmptyStmt && elsStmt == EmptyStmt)) {
        If(cond, Seqn(Seq(thnStmt), Nil)(), Seqn(Seq(elsStmt), Nil)())()
      } else {
        EmptyStmt
      }
      val stmts = Seq(condStmt, ifStmt).filterNot(_ == EmptyStmt)
      Seqn(stmts, Nil)()
    case (Unfolding(acc, unfBody), c) =>
      val permCheck = transformExp(acc.perm, c)
      val unfoldBody = transformExp(unfBody, c)
      // only unfold and fold if body contains something
      val (unfold, fold) = if (unfoldBody != EmptyStmt){
          (Unfold(acc)(), Fold(acc)())
        } else {
          (EmptyStmt, EmptyStmt)
        }
      val stmts = Seq(permCheck, unfold, unfoldBody, fold).filterNot(_ == EmptyStmt)
      Seqn(stmts, Nil)()

    case (inex: InhaleExhaleExp, c) =>
      val inhaleStmt = transformExp(inex.in, c)
      val exhaleStmt = transformExp(inex.ex, c)



      if (!(inhaleStmt == EmptyStmt && exhaleStmt == EmptyStmt)) {
        c.conditionInEx match {
          case Some(conditionVar) => If(conditionVar.localVar, Seqn(Seq(inhaleStmt), Nil)(), Seqn(Seq(exhaleStmt), Nil)())()
          case None => Seqn(Seq(inhaleStmt, exhaleStmt), Nil)()
        }
      } else {
        EmptyStmt
      }
    case (letExp: Let, c) =>
      val expressionStmt = transformExp(letExp.exp, c)
      val localVarDecl = letExp.variable

      val inhaleEq = Inhale(EqCmp(localVarDecl.localVar, letExp.exp)())()

      val bodyStmt = transformExp(letExp.body, c)

      Seqn(Seq(expressionStmt, inhaleEq, bodyStmt), Seq(localVarDecl))()

    case (b: BinExp, c) =>
      val left = transformExp(b.left, c)
      val right = transformExp(b.right, c)

      // Short circuit evaluation
      val rightSCE = if (right != EmptyStmt) {
        b match {
          case _: Or =>
            If(Not(b.left)(), Seqn(Seq(right), Nil)(), EmptyStmt)()
          case _: And =>
            If(b.left, Seqn(Seq(right), Nil)(), EmptyStmt)()
          case _: Implies =>
            If(b.left, Seqn(Seq(right), Nil)(), EmptyStmt)()
          case _ =>
            Seqn(Seq(left, right), Nil)(b.pos)
        }
      } else {
        EmptyStmt
      }
      val stmts = Seq(left, rightSCE).filterNot(_ == EmptyStmt)
      Seqn(stmts, Nil)()
    case (sq: SeqExp, c) => sq match {
      case ExplicitSeq(elems) =>
        Seqn(elems.map(transformExp(_, c)), Nil)(sq.pos)
      case RangeSeq(low, high) =>
        Seqn(Seq(transformExp(low, c),
          transformExp(high, c)), Nil)(sq.pos)
      case SeqAppend(left, right) =>
        Seqn(Seq(transformExp(left, c),
          transformExp(right, c)), Nil)(sq.pos)
      case SeqIndex(s, idx) =>
        Seqn(Seq(transformExp(s, c),
          transformExp(idx, c)), Nil)(sq.pos)
      case SeqTake(s, n) =>
        Seqn(Seq(transformExp(s, c),
          transformExp(n, c)), Nil)(sq.pos)
      case SeqDrop(s, n) =>
        Seqn(Seq(transformExp(s, c),
          transformExp(n, c)), Nil)(sq.pos)
      case SeqContains(elem, s) =>
        Seqn(Seq(transformExp(elem, c),
          transformExp(s, c)), Nil)(sq.pos)
      case SeqUpdate(s, idx, elem) =>
        Seqn(Seq(transformExp(s, c),
          transformExp(idx, c),
          transformExp(elem, c)), Nil)(sq.pos)
      case SeqLength(s) =>
        Seqn(Seq(transformExp(s, c)), Nil)(sq.pos)
      case EmptySeq(e) => EmptyStmt

      case unsupportedExp => reportUnsupportedExp(unsupportedExp)
        EmptyStmt
    }
    case (st: ExplicitSet, c) =>
      Seqn(st.elems.map(transformExp(_, c)), Nil)(st.pos)
    case (mst: ExplicitMultiset, c) =>
      Seqn(mst.elems.map(transformExp(_, c)), Nil)(mst.pos)
    case (u: UnExp, c) => transformExp(u.exp, c)

    case (l: Literal, c) => EmptyStmt
    case (v: AbstractLocalVar, c) => EmptyStmt
    case (p: AbstractConcretePerm, c) => EmptyStmt
    case (la: LocationAccess, c) => EmptyStmt

    case (ap: AccessPredicate, c) =>
      transformExp(ap.perm, c)

    case (fa: FuncLikeApp, c) =>
      val argStmts = fa.args.map(transformExp(_,c)).filterNot(_ == EmptyStmt)
      Seqn(argStmts, Nil)()
    case (unsupportedExp, c) =>
      if (c.unsupportedOperationException){
        reportUnsupportedExp(unsupportedExp)
        EmptyStmt
      } else {
        val sub = unsupportedExp.subExps.map(transformExp(_, c)).filterNot(_ == EmptyStmt)
        Seqn(sub, Nil)()
      }
  }

  /**
    * Issues a consistency error for unsupported expressions.
    * @param unsupportedExp to be reported.
    */
  def reportUnsupportedExp(unsupportedExp: Exp): Unit ={
    reportError(ConsistencyError("Unsupported expression detected: " + unsupportedExp + ", " + unsupportedExp.getClass, unsupportedExp.pos))
  }

}

trait ExpressionContext {
  val unsupportedOperationException: Boolean
  val conditionInEx: Option[LocalVarDecl]
}