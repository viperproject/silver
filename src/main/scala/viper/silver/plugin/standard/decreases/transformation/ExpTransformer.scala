// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.decreases.transformation

import viper.silver.ast.{Exp, Stmt, _}
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.{ContextCustom, SimpleContext, Strategy, Traverse}

/**
 * A basic interface which helps to rewrite an expression (e.g. a function body) into a stmt (e.g. for a method body).
 * Some default transformations are already implemented.
 */
trait ExpTransformer extends ErrorReporter {

  /**
   * Transforms an expression into a statement.
   *
   * @return a statement representing the expression
   */
  def transformExp: PartialFunction[(Exp, ExpressionContext), Stmt] = {
    case (CondExp(cond, thn, els), c) =>
      val condStmt = transformExp(cond, c)
      val thnStmt = transformExp(thn, c)
      val elsStmt = transformExp(els, c)

      val ifStmt = If(cond, Seqn(Seq(thnStmt), Nil)(), Seqn(Seq(elsStmt), Nil)())()

      val stmts = Seq(condStmt, ifStmt)
      Seqn(stmts, Nil)()
    case (Unfolding(acc, unfBody), c) =>
      val permCheck = transformExp(acc.perm, c)
      val unfoldBody = transformExp(unfBody, c)
      // only unfold and fold if body contains something
      val (unfold, fold) = (Unfold(acc)(), Fold(acc)())

      val stmts = Seq(permCheck, unfold, unfoldBody, fold).filterNot(_ == EmptyStmt)
      Seqn(stmts, Nil)()

    case (inex: InhaleExhaleExp, c) =>
      val inhaleStmt = transformExp(inex.in, c)
      val exhaleStmt = transformExp(inex.ex, c)

      c.conditionInEx match {
        case Some(conditionVar) => If(conditionVar.localVar, Seqn(Seq(inhaleStmt), Nil)(), Seqn(Seq(exhaleStmt), Nil)())()
        case None => Seqn(Seq(inhaleStmt, exhaleStmt), Nil)()
      }
    case (letExp: Let, c) =>
      val expressionStmt = transformExp(letExp.exp, c)
      val localVarDecl = letExp.variable

      val inhaleEq = Inhale(EqCmp(localVarDecl.localVar, letExp)())()

      val bodyStmt = transformExp(letExp.body, c)

      Seqn(Seq(expressionStmt, inhaleEq, bodyStmt), Seq(localVarDecl))()

    case (b: BinExp, c) =>
      val left = transformExp(b.left, c)
      val right = transformExp(b.right, c)

      // Short circuit evaluation
      val rightSCE = b match {
        case _: Or =>
          val sanLeft: Exp = sanitiseBooleanExp(c).execute(b.left)
          If(Not(sanLeft)(), Seqn(Seq(right), Nil)(), EmptyStmt)()
        case _: And =>
          val sanLeft: Exp = sanitiseBooleanExp(c).execute(b.left)
          If(sanLeft, Seqn(Seq(right), Nil)(), EmptyStmt)()
        case _: Implies =>
          val sanLeft: Exp = sanitiseBooleanExp(c).execute(b.left)
          If(sanLeft, Seqn(Seq(right), Nil)(), EmptyStmt)()
        case _ =>
          Seqn(Seq(right), Nil)()
      }
      val stmts = Seq(left, rightSCE)
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

      val inhale = Inhale(ap)(ap.pos)

      Seqn(Seq(check, inhale), Nil)()

    case (fa: FuncLikeApp, c) =>
      val argStmts = fa.args.map(transformExp(_, c))
      Seqn(argStmts, Nil)()
    case (unsupportedExp, c) =>
      transformExpUnknown(unsupportedExp, c)
  }

  /**
   * Expression transformer if no default is defined.
   * Calls transformExp on all subExps of e.
   * To change or extend the default transformer for unknown expressions
   * override this method (and possibly combine it with super.transformExpUnknown).
   */
  def transformExpUnknown(e: Exp, c: ExpressionContext): Stmt = {
    val sub = e.subExps.map(transformExp(_, c)).filterNot(_ == EmptyStmt)
    Seqn(sub, Nil)()
  }

  /**
   * AccessPredicate and MagicWands expressions are removed by replacing them with TrueLit.
   * If a conditionInEx is given in the context the InhaleExhaleExp are conditionally divided,
   * otherwise they are combined with an Or.
   */
  def sanitiseBooleanExp(c: ExpressionContext): Strategy[Node, ContextCustom[Node, ExpressionContext]] =
    ViperStrategy.CustomContext(sanitiseBooleanExpRewriting, c, Traverse.Innermost)
      .recurseFunc(sanitiseBooleanExpRecursion)

  val sanitiseBooleanExpRewriting: PartialFunction[(Node, ExpressionContext), (Node, ExpressionContext)] = {
    case (inexExp: InhaleExhaleExp, c) =>
      val newInexExp = c.conditionInEx match {
        case Some(conditionInEx) =>
          CondExp(conditionInEx.localVar, inexExp.in, inexExp.ex)(inexExp.pos)
        case None =>
          Or(inexExp.in, inexExp.ex)(inexExp.pos)
      }
      (newInexExp, c)
    case (_: AccessPredicate | _: MagicWand, c) => (TrueLit()(), c)
  }

  val sanitiseBooleanExpRecursion: PartialFunction[Node, Seq[Node]] = {
    case Unfolding(_, body) => Seq(body)
  }


  /**
   * The simplifyStmts Strategy can be used to simplify statements
   * by e.g. removing or combining nested Seqn or If clauses.
   * This is in particular useful for the expression to statement transformer
   * because this often creates nested and empty Seqn and If clauses
   */
  val simplifyStmts: Strategy[Node, SimpleContext[Node]] = ViperStrategy.Slim({
    case Seqn(EmptyStmt, _) => // remove empty Seqn (including unnecessary scopedDecls)
      EmptyStmt
    case Seqn(Seq(Seqn(ss, scopedDecls2)), scopedDecls1) => // combine nested Seqn
      Seqn(ss, scopedDecls1 ++ scopedDecls2)()
    case Seqn(ss, scopedDecls) => // remove empty statements
      Seqn(ss.filterNot(_ == EmptyStmt), scopedDecls)()
    case If(_, EmptyStmt, EmptyStmt) => // remove empty If clause
      EmptyStmt
    case If(c, EmptyStmt, els) => // change If with only els to If with only thn
      If(Not(c)(c.pos), els, EmptyStmt)()
    case If(c1, Seqn(Seq(If(c2, thn, EmptyStmt)), Nil), EmptyStmt) => // combine nested if clauses
      If(And(c1, c2)(), thn, EmptyStmt)()
  }, Traverse.BottomUp)
}

trait ExpressionContext {
  val conditionInEx: Option[LocalVarDecl]
}