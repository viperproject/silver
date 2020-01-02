// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.decreases.transformation

import viper.silver.ast.{Exp, Stmt, _}
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.{ContextCustom, Strategy}
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
        val sanCond: Exp = sanitiseExpStrategy(c).execute(cond)
        If(sanCond, Seqn(Seq(thnStmt), Nil)(), Seqn(Seq(elsStmt), Nil)())()
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
          val sanAcc: PredicateAccessPredicate = sanitiseExpStrategy(c).execute(acc)
          (Unfold(sanAcc)(), Fold(sanAcc)())
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

      val sanExp: Exp = sanitiseExpStrategy(c).execute(letExp.exp)

      val inhaleEq = Inhale(EqCmp(localVarDecl.localVar, sanExp)())()

      val bodyStmt = transformExp(letExp.body, c)

      Seqn(Seq(expressionStmt, inhaleEq, bodyStmt), Seq(localVarDecl))()

    case (b: BinExp, c) =>
      val left = transformExp(b.left, c)
      val right = transformExp(b.right, c)

      // Short circuit evaluation
      val rightSCE = if (right != EmptyStmt) {
        b match {
          case _: Or if b.left.isPure =>
            val sanLeft: Exp = sanitiseExpStrategy(c).execute(b.left)
            If(Not(sanLeft)(), Seqn(Seq(right), Nil)(), EmptyStmt)()
          case _: And if b.left.isPure =>
            val sanLeft: Exp = sanitiseExpStrategy(c).execute(b.left)
            If(sanLeft, Seqn(Seq(right), Nil)(), EmptyStmt)()
          case _: Implies if b.left.isPure  =>
            val sanLeft: Exp = sanitiseExpStrategy(c).execute(b.left)
            If(sanLeft, Seqn(Seq(right), Nil)(), EmptyStmt)()
          case _ =>
            Seqn(Seq(right), Nil)()
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

      case unsupportedExp => transformExpUnknown(unsupportedExp, c)
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
      val check = transformExp(ap.perm, c)

      val sanAp: Exp = sanitiseExpStrategy(c).execute(ap)
      val inhale = Inhale(sanAp)(ap.pos)

      Seqn(Seq(check, inhale), Nil)()

    case (fa: FuncLikeApp, c) =>
      val argStmts = fa.args.map(transformExp(_,c)).filterNot(_ == EmptyStmt)
      Seqn(argStmts, Nil)()
    case (unsupportedExp, c) =>
      transformExpUnknown(unsupportedExp, c)
  }

  /**
   * Expression transformer if no default is defined.
   * Calls transformExp on all subExps of e.
   * Can be overridden if another operation is required.
   */
  def transformExpUnknown(e: Exp, c: ExpressionContext): Stmt = {
    val sub = e.subExps.map(transformExp(_, c)).filterNot(_ == EmptyStmt)
    Seqn(sub, Nil)()
  }

  /**
   * Sanitizes expressions to be used in the statement.
   */
  def sanitiseExp: PartialFunction[(Node, ExpressionContext), (Node, ExpressionContext)] = {
    case (inexExp: InhaleExhaleExp, c) =>
      val newInexExp = c.conditionInEx match {
        case Some(conditionInEx) =>
          CondExp(conditionInEx.localVar, inexExp.in, inexExp.ex)(inexExp.pos)
        case None =>
          Or(inexExp.in, inexExp.ex)(inexExp.pos)
      }
      (newInexExp, c)
  }

  final def sanitiseExpStrategy(c: ExpressionContext): Strategy[Node, ContextCustom[Node, ExpressionContext]] = ViperStrategy.CustomContext(sanitiseExp, c)
}

trait ExpressionContext {
  val conditionInEx: Option[LocalVarDecl]
}