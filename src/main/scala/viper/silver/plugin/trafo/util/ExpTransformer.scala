// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.trafo.util

import viper.silver.ast._
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.verifier.ConsistencyError

/**
  * A basic interface which helps to rewrite an expression (e.g. a function body) into a stmt (e.g. for a method body).
  * Some basic transformations are already implemented.
  * If no transformation is defined for an expression a consistency error is reported (to avoid unsound results).
  */
trait ExpTransformer extends PredicateInstanceManager {

  /**
    * Transforms an expression (e.g. function body) into a statement.
    * If an unsupported expression is detected, i.e. an expression for which no transformation is defined,
    * a consistency error is reported (to avoid unsound results).
    * Parts of the expressions which stay expressions (e.g. the condition in a if clause)
    * are also transformed into statements and prepended to the other statement.
    * @return a statement representing the expression
    */
  def transformExp: PartialFunction[(Exp, Context), Stmt] = {
    case (CondExp(cond, thn, els), c) =>
      val condStmt = transformExp(cond, c)
      val thnStmt = transformExp(thn, c)
      val elsStmt = transformExp(els, c)
      val ifStmt = If(cond, Seqn(Seq(thnStmt), Nil)(), Seqn(Seq(elsStmt), Nil)())()
      Seqn(Seq(condStmt, ifStmt), Nil)()
    case (Unfolding(acc, unfBody), c) =>
      val permCheck = transformExp(acc.perm, c)
      val unfold = generateUnfoldNested(acc)
      val unfoldBody = transformExp(unfBody, c)
      val fold = Fold(acc)()
      Seqn(Seq(permCheck, unfold, unfoldBody, fold), Nil)()
    case (b: BinExp, c) =>
      val left = transformExp(b.left, c)
      val right = transformExp(b.right, c)
      // Short circuit evaluation
      b match {
        case _: Or =>
          Seqn(Seq(left,
            If(Not(b.left)(b.pos), Seqn(Seq(right), Nil)(b.pos), EmptyStmt)(b.pos)),
            Nil)(b.pos)
        case _: And =>
          Seqn(Seq(left,
            If(b.left, Seqn(Seq(right), Nil)(b.pos), EmptyStmt)(b.pos)),
            Nil)(b.pos)
        case _: Implies =>
          Seqn(Seq(left,
            If(b.left, Seqn(Seq(right), Nil)(b.pos), EmptyStmt)(b.pos)),
            Nil)(b.pos)
        case _ =>
          Seqn(Seq(left, right), Nil)(b.pos)
      }
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
    case (dc: DomainFuncApp, c) => EmptyStmt
    case (p: AbstractConcretePerm, c) => EmptyStmt
    case (la: LocationAccess, c) => EmptyStmt

    case (unsupportedExp, c) => reportUnsupportedExp(unsupportedExp)
      EmptyStmt
  }

  /**
    * Issues a consistency error for unsupported expressions.
    * @param unsupportedExp to be reported.
    */
  def reportUnsupportedExp(unsupportedExp: Exp): Unit ={
    reportError(ConsistencyError("Unsupported expression detected: " + unsupportedExp + ", " + unsupportedExp.getClass, unsupportedExp.pos))
  }

}

trait Context