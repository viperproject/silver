// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import viper.silver.ast._
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast.utility.{Expressions, ViperStrategy}
import viper.silver.ast.utility.rewriter.{ContextCustom, Strategy, Traverse}
import viper.silver.verifier.ConsistencyError

/**
 * A basic interface which helps to rewrite an expression (e.g. a function body) into a stmt (e.g. for a method body).
 * Some default transformations are already implemented.
 */
trait ExpTransformer extends ProgramManager with ErrorReporter {

  /**
   * Transforms an expression into a statement that checks the termination conditions for that expression.
   * If inhaleExp is true, the expression is inhaled during the check.
   *
   * @return a statement representing the expression.
   */
  def transformExp(e: Exp, c: ExpressionContext, inhaleExp: Boolean): Stmt = e match {
    case And(fst, snd) if inhaleExp =>
      // Special case conjunctions s.t. we properly inhale the first expression before checking the second.
      // This is necessary if fst contains e.g. a quantified permission, and snd is well-defined only if that quantified
      // permission is available.
      val fstStmt = transformExp(fst, c, inhaleExp)
      val nonDetVarDecl = LocalVarDecl(uniqueName("b"), Bool)(e.pos, e.info, e.errT)
      val assumeFalse = Inhale(FalseLit()())()
      val inhaleFst = Inhale(fst)()
      val inhaleFstStmt = if (fst.contains[InhaleExhaleExp]) {
        c.conditionInEx match {
          case Some(conditionVar) => If(conditionVar.localVar, Seqn(Seq(inhaleFst), Nil)(), Seqn(Seq(Inhale(fst.whenExhaling)()), Nil)())()
          case None => inhaleFst
        }
      } else {
        inhaleFst
      }
      val fstIf = If(nonDetVarDecl.localVar, Seqn(Seq(fstStmt, assumeFalse), Nil)(), Seqn(Seq(inhaleFstStmt), Nil)())(e.pos, e.info, e.errT)
      val fstBlock = Seqn(Seq(fstIf), Seq(nonDetVarDecl))()
      val sndStmt = transformExp(snd, c, inhaleExp)
      Seqn(Seq(fstBlock, sndStmt), Nil)()

    case CondExp(cond, thn, els) =>
      val condStmt = transformExp(cond, c, false)
      val thnStmt = transformExp(thn, c, inhaleExp)
      val elsStmt = transformExp(els, c, inhaleExp)
      val ifStmt = if (isEmptyStatement(thnStmt) && isEmptyStatement(elsStmt))
        EmptyStmt
      else
        If(cond, Seqn(Seq(thnStmt), Nil)(), Seqn(Seq(elsStmt), Nil)())()
      val stmts = Seq(condStmt, ifStmt)
      Seqn(stmts, Nil)()

    case Unfolding(acc, unfBody) =>
      val permCheck = transformExp(acc.perm, c, false)
      val unfoldBody = transformExp(unfBody, c, inhaleExp)
      val unfold = Unfold(acc)()
      val nonDetVarDecl = LocalVarDecl(uniqueName("b"), Bool)(e.pos, e.info, e.errT)
      val assumeFalse = Inhale(FalseLit()())()
      val unfoldPart = if (!isEmptyStatement(unfoldBody)) Seqn(Seq(unfold, unfoldBody), Nil)() else EmptyStmt
      val thenBranch = Seqn(Seq(permCheck, unfoldPart, assumeFalse), Nil)()
      val elseBranch = if (inhaleExp) Seqn(Seq(Inhale(e)(e.pos, e.info)), Nil)() else EmptyStmt
      if (isEmptyStatement(permCheck) && isEmptyStatement(unfoldPart))
        elseBranch
      else
        Seqn(Seq(If(nonDetVarDecl.localVar, thenBranch, elseBranch)()), Seq(nonDetVarDecl))()

    case Applying(wand, body) =>
      // note that this case is untested -- it's not possible to write a function with an `applying` expression
      val nonDetVarDecl = LocalVarDecl(uniqueName("b"), Bool)(e.pos, e.info, e.errT)
      val bodyStmt = transformExp(body, c, inhaleExp)
      val killBranchStmt = Inhale(FalseLit()(e.pos, e.info, e.errT))(e.pos, e.info, e.errT)
      val thnStmt = Seqn(Seq(Apply(wand)(e.pos, e.info, e.errT), bodyStmt, killBranchStmt), Nil)()
      val ifStmt = If(nonDetVarDecl.localVar, thnStmt, EmptyStmt)(e.pos, e.info, e.errT)
      Seqn(Seq(ifStmt), Seq(nonDetVarDecl))(e.pos, e.info, e.errT)

    case inex: InhaleExhaleExp =>
      val inhaleStmt = transformExp(inex.in, c, inhaleExp)
      val exhaleStmt = transformExp(inex.ex, c, inhaleExp)

      c.conditionInEx match {
        case Some(conditionVar) => If(conditionVar.localVar, Seqn(Seq(inhaleStmt), Nil)(), Seqn(Seq(exhaleStmt), Nil)())()
        case None => Seqn(Seq(inhaleStmt, exhaleStmt), Nil)()
      }

    case letExp: Let =>
      val expressionStmt = transformExp(letExp.exp, c, false)
      val localVarDecl = letExp.variable

      val inhaleEq = Inhale(EqCmp(localVarDecl.localVar, letExp.exp)())()

      val bodyStmt = transformExp(letExp.body, c, inhaleExp)

      val bodyCheck  = if (isEmptyStatement(bodyStmt))
        EmptyStmt
      else
        Seqn(Seq(inhaleEq, bodyStmt), Seq(localVarDecl))()

      Seqn(Seq(expressionStmt, bodyCheck), Nil)()

    case b: BinExp =>
      val left = transformExp(b.left, c, inhaleExp)
      val right = transformExp(b.right, c, inhaleExp)

      // Short circuit evaluation
      val pureLeft: Exp = toPureBooleanExp(c).execute(b.left)
      val rightSCE = if (isEmptyStatement(right)) EmptyStmt else b match {
        case _: Or =>
          If(Not(pureLeft)(), Seqn(Seq(right), Nil)(), EmptyStmt)()
        case _: And =>
          If(pureLeft, Seqn(Seq(right), Nil)(), EmptyStmt)()
        case _: Implies =>
          If(pureLeft, Seqn(Seq(right), Nil)(), EmptyStmt)()
        case _ =>
          Seqn(Seq(right), Nil)()
      }
      Seqn(Seq(left, rightSCE), Nil)()

    case _: Literal => EmptyStmt
    case _: AbstractLocalVar => EmptyStmt
    case _: AbstractConcretePerm => EmptyStmt
    case _: WildcardPerm => EmptyStmt
    case _: EpsilonPerm => EmptyStmt
    case _: CurrentPerm => EmptyStmt
    case _: LocationAccess => EmptyStmt

    case ap: AccessPredicate =>
      val check = transformExp(ap.perm, c, false)
      val inhale = Inhale(ap)(ap.pos)
      Seqn(Seq(check, inhale), Nil)()

    case fa: Forall =>
      // we turn the quantified variables into local variables with arbitrary value and show that the expression holds
      // for arbitrary values, which is similar to a forall introduction
      val (localDeclMapping, transformedExp) = substituteWithFreshVars(fa.variables, fa.exp)
      val expressionStmt = transformExp(transformedExp, c, inhaleExp)
      Seqn(Seq(expressionStmt), localDeclMapping.map(_._2))(fa.pos, fa.info, fa.errT)

    case fp: ForPerm =>
      // let's pick arbitrary values for the quantified variables and check the body given that the current heap has
      // sufficient permissions
      val (localDeclMapping, transformedExp) = substituteWithFreshVars(fp.variables, fp.exp)
      val transformedRes = applySubstitution(localDeclMapping, fp.resource)
      val expressionStmt = transformExp(transformedExp, c, inhaleExp)
      val killBranchStmt = Inhale(FalseLit()(e.pos, e.info, e.errT))(e.pos, e.info, e.errT)
      val thnStmt = Seqn(Seq(expressionStmt, killBranchStmt), Nil)(e.pos, e.info, e.errT)
      val ifCond = GtCmp(CurrentPerm(transformedRes)(e.pos, e.info, e.errT), NoPerm()(e.pos, e.info, e.errT))(e.pos, e.info, e.errT)
      val ifStmt = If(ifCond, thnStmt, EmptyStmt)(e.pos, e.info, e.errT)
      Seqn(Seq(ifStmt), localDeclMapping.map(_._2))(e.pos, e.info, e.errT)

    case ex: Exists =>
      // we perform existential elimination by retrieving witnesses for the quantified variables
      val (localDeclMapping, transformedExp) = substituteWithFreshVars(ex.variables, ex.exp)
      // we can't use an assume statement at this point because the `assume`s have already been rewritten
      // furthermore, Viper only allows pure existentially quantified expressions
      val inhaleWitnesses = Inhale(transformedExp)(ex.pos, ex.info, ex.errT)
      val expressionStmt = transformExp(transformedExp, c, inhaleExp)
      Seqn(Seq(inhaleWitnesses, expressionStmt), localDeclMapping.map(_._2))(ex.pos, ex.info, ex.errT)

    case fa: FuncLikeApp =>
      val argStmts = fa.args.map(transformExp(_, c, false))
      Seqn(argStmts, Nil)()

    case e: ExtensionExp => reportUnsupportedExp(e)

    case _ =>
      val sub = e.subExps.map(transformExp(_, c, false))
      Seqn(sub, Nil)()
  }

  def isEmptyStatement(stmt: Stmt): Boolean = stmt match {
    case Seqn(stmts, _) => stmts.forall(isEmptyStatement)
    case _ => false
  }

  /**
    * Issues a consistency error for unsupported expressions.
    *
    * @param unsupportedExp to be reported.
    */
  def reportUnsupportedExp(unsupportedExp: Exp): Stmt = {
    reportError(ConsistencyError("Unsupported expression detected: " + unsupportedExp + ", " + unsupportedExp.getClass, unsupportedExp.pos))
    EmptyStmt
  }

  /**
   * Transforms boolean expressions to pure boolean expression,
   * such that they can be used as conditions in if clauses.
   *
   * AccessPredicate and MagicWands expressions are removed by replacing them with TrueLit.
   * InhaleExhaleExp is conditionally divided if a conditionInEx is given (in the context),
   * otherwise they are combined with an Or.
   */
  protected def toPureBooleanExp(c: ExpressionContext): Strategy[Node, ContextCustom[Node, ExpressionContext]] =
    ViperStrategy.CustomContext(toPureBooleanExpRewriting, c, Traverse.TopDown)
      .recurseFunc(toPureBooleanExpRecursion)

  private val toPureBooleanExpRewriting: PartialFunction[(Node, ExpressionContext), (Node, ExpressionContext)] = {
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

  private val toPureBooleanExpRecursion: PartialFunction[Node, Seq[Node]] = {
    case Unfolding(_, body) => Seq(body)
    case _: AccessPredicate | _: MagicWand => Nil
    case Applying(_, b) => Seq(b)
    case Forall(_, _, exp) => Seq(exp)
  }

  /**
    * Turns `vars` into new local variable declarations with a unique name and replaces the corresponding local variable uses in `exp`.
    * Returns a mapping of old variable declarations to new ones and the transformed expression
    */
  protected def substituteWithFreshVars[E <: Exp](vars: Seq[LocalVarDecl], exp: E): (Seq[(LocalVarDecl, LocalVarDecl)], E) = {
    val declMapping = vars.map(oldDecl =>
      oldDecl -> LocalVarDecl(uniqueName(oldDecl.name), oldDecl.typ)(oldDecl.pos, oldDecl.info, oldDecl.errT))
    val transformedExp = applySubstitution(declMapping, exp)
    (declMapping, transformedExp)
  }

  /**
    * Replaces uses of local variables in `exp` based on `mapping`.
    * `mapping` maps local variable declarations to new declarations and this transformation replaces the corresponding
    * local variable uses.
    */
  protected def applySubstitution[E <: Exp](mapping: Seq[(LocalVarDecl, LocalVarDecl)], exp: E): E = {
    Expressions.instantiateVariables(exp, mapping.map(_._1.localVar), mapping.map(_._2.localVar))
  }
}

trait ExpressionContext {
  val conditionInEx: Option[LocalVarDecl]
}
