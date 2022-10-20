// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import viper.silver.ast.{And, AnySetExp, Exp, Stmt, _}
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.{ContextCustom, RepeatedStrategy, Strategy, Traverse}
import viper.silver.verifier.ConsistencyError

/**
 * A basic interface which helps to rewrite an expression (e.g. a function body) into a stmt (e.g. for a method body).
 * Some default transformations are already implemented.
 */
trait ExpTransformer extends ProgramManager with ErrorReporter {

  /**
   * Transforms an expression into a statement.
   *
   * @return a statement representing the expression.
   */
  def transformExp(e: Exp, c: ExpressionContext): Stmt = e match {
    case CondExp(cond, thn, els) =>
      val condStmt = transformExp(cond, c)
      val thnStmt = transformExp(thn, c)
      val elsStmt = transformExp(els, c)

      val ifStmt = If(cond, Seqn(Seq(thnStmt), Nil)(), Seqn(Seq(elsStmt), Nil)())()

      val stmts = Seq(condStmt, ifStmt)
      Seqn(stmts, Nil)()
    case Unfolding(acc, unfBody) =>
      val permCheck = transformExp(acc.perm, c)
      val unfoldBody = transformExp(unfBody, c)
      // only unfold and fold if body contains something
      val (unfold, fold) = (Unfold(acc)(), Fold(acc)())

      val stmts = Seq(permCheck, unfold, unfoldBody, fold)
      Seqn(stmts, Nil)()
    case Applying(wand, body) =>
      // note that this case is untested -- it's not possible to write a function with an `applying` expression
      val nonDetVarDecl = LocalVarDecl(uniqueName("b"), Bool)(e.pos, e.info, e.errT)
      val bodyStmt = transformExp(body, c)
      val killBranchStmt = Inhale(FalseLit()(e.pos, e.info, e.errT))(e.pos, e.info, e.errT)
      val thnStmt = Seqn(Seq(Apply(wand)(e.pos, e.info, e.errT), bodyStmt, killBranchStmt), Nil)()
      val ifStmt = If(nonDetVarDecl.localVar, thnStmt, EmptyStmt)(e.pos, e.info, e.errT)
      Seqn(Seq(ifStmt), Seq(nonDetVarDecl))(e.pos, e.info, e.errT)
    case inex: InhaleExhaleExp =>
      val inhaleStmt = transformExp(inex.in, c)
      val exhaleStmt = transformExp(inex.ex, c)

      c.conditionInEx match {
        case Some(conditionVar) => If(conditionVar.localVar, Seqn(Seq(inhaleStmt), Nil)(), Seqn(Seq(exhaleStmt), Nil)())()
        case None => Seqn(Seq(inhaleStmt, exhaleStmt), Nil)()
      }
    case letExp: Let =>
      val expressionStmt = transformExp(letExp.exp, c)
      val localVarDecl = letExp.variable

      val inhaleEq = Inhale(EqCmp(localVarDecl.localVar, letExp.exp)())()

      val bodyStmt = transformExp(letExp.body, c)

      Seqn(Seq(expressionStmt, inhaleEq, bodyStmt), Seq(localVarDecl))()

    case b: BinExp =>
      val left = transformExp(b.left, c)
      val right = transformExp(b.right, c)

      // Short circuit evaluation
      val pureLeft: Exp = toPureBooleanExp(c).execute(b.left)
      val rightSCE = b match {
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
    case ase: AnySetExp => ase match {
      case exp: AnySetUnExp => Seqn(Seq(transformExp(exp.exp, c)), Nil)(ase.pos)
      case exp: AnySetBinExp => Seqn(Seq(transformExp(exp.left, c), transformExp(exp.right, c)), Nil)(ase.pos)
      case MapDomain(base) => Seqn(Seq(transformExp(base, c)), Nil)(ase.pos)
      case MapRange(base) => Seqn(Seq(transformExp(base, c)), Nil)(ase.pos)
    }
    // remaining `SetExp`:
    case EmptySet(_) => EmptyStmt
    case e@ExplicitSet(elems) => Seqn(elems.map(transformExp(_, c)), Nil)(e.pos)
    // remaining `MultisetExp`:
    case EmptyMultiset(_) => EmptyStmt
    case e@ExplicitMultiset(elems) => Seqn(elems.map(transformExp(_, c)), Nil)(e.pos)
    // remaining `SeqExp`:
    case EmptySeq(_) => EmptyStmt
    case e@ExplicitSeq(elems) => Seqn(elems.map(transformExp(_, c)), Nil)(e.pos)
    case e@RangeSeq(low, high) => Seqn(Seq(transformExp(low, c), transformExp(high, c)), Nil)(e.pos)
    case e@SeqAppend(left, right) => Seqn(Seq(transformExp(left, c), transformExp(right, c)), Nil)(e.pos)
    case e@SeqIndex(s, idx) => Seqn(Seq(transformExp(s, c), transformExp(idx, c)), Nil)(e.pos)
    case e@SeqTake(s, n) => Seqn(Seq(transformExp(s, c), transformExp(n, c)), Nil)(e.pos)
    case e@SeqDrop(s, n) => Seqn(Seq(transformExp(s, c), transformExp(n, c)), Nil)(e.pos)
    case e@SeqContains(elem, s) => Seqn(Seq(transformExp(elem, c), transformExp(s, c)), Nil)(e.pos)
    case e@SeqUpdate(s, idx, elem) => Seqn(Seq(transformExp(s, c), transformExp(idx, c), transformExp(elem, c)), Nil)(e.pos)
    case e@SeqLength(s) => Seqn(Seq(transformExp(s, c)), Nil)(e.pos)
    // remaining `MapExp`:
    case EmptyMap(_, _) => EmptyStmt
    case e@ExplicitMap(elems) => Seqn(elems.map(transformExp(_, c)), Nil)(e.pos)
    case e@Maplet(key, value) => Seqn(Seq(transformExp(key, c), transformExp(value, c)), Nil)(e.pos)
    case e@MapCardinality(base) => Seqn(Seq(transformExp(base, c)), Nil)(e.pos)
    case e@MapContains(key, base) => Seqn(Seq(transformExp(key, c), transformExp(base, c)), Nil)(e.pos)
    case e@MapLookup(base, key) => Seqn(Seq(transformExp(base, c), transformExp(key, c)), Nil)(e.pos)
    case e@MapUpdate(base, key, value) => Seqn(Seq(transformExp(base, c), transformExp(key, c), transformExp(value, c)), Nil)(e.pos)

    case u: UnExp => transformExp(u.exp, c)
    case _: Literal => EmptyStmt
    case _: AbstractLocalVar => EmptyStmt
    case _: AbstractConcretePerm => EmptyStmt
    case _: WildcardPerm => EmptyStmt
    case _: EpsilonPerm => EmptyStmt
    case _: CurrentPerm => EmptyStmt
    case _: LocationAccess => EmptyStmt

    case ap: AccessPredicate =>
      val check = transformExp(ap.perm, c)
      val inhale = Inhale(ap)(ap.pos)
      Seqn(Seq(check, inhale), Nil)()
    case fa: Forall =>
      // we turn the quantified variables into local variables with arbitrary value and show that the expression holds
      // for arbitrary values, which is similar to a forall introduction
      val (freshDecls, transformedExp, _) = substituteWithFreshVars(fa.variables, fa.exp)
      val expressionStmt = transformExp(transformedExp, c)
      Seqn(Seq(expressionStmt), freshDecls)(fa.pos, fa.info, fa.errT)
    case fp: ForPerm =>
      // let's pick arbitrary values for the quantified variables and check the body given that the current heap has
      // sufficient permissions
      val (freshDecls, transformedExp, varMapping) = substituteWithFreshVars(fp.variables, fp.exp)
      val transformedRes = substituteVars(varMapping, fp.resource)
      val expressionStmt = transformExp(transformedExp, c)
      val killBranchStmt = Inhale(FalseLit()(e.pos, e.info, e.errT))(e.pos, e.info, e.errT)
      val thnStmt = Seqn(Seq(expressionStmt, killBranchStmt), Nil)(e.pos, e.info, e.errT)
      val ifCond = GtCmp(CurrentPerm(transformedRes)(e.pos, e.info, e.errT), NoPerm()(e.pos, e.info, e.errT))(e.pos, e.info, e.errT)
      val ifStmt = If(ifCond, thnStmt, EmptyStmt)(e.pos, e.info, e.errT)
      Seqn(Seq(ifStmt), freshDecls)(e.pos, e.info, e.errT)
    case ex: Exists =>
      // we perform existential elimination by retrieving witnesses for the quantified variables
      val (freshDecls, transformedExp, _) = substituteWithFreshVars(ex.variables, ex.exp)
      // we can't use an assume statement at this point because the `assume`s have already been rewritten
      // furthermore, Viper only allows pure existentially quantified expressions
      val inhaleWitnesses = Inhale(transformedExp)(ex.pos, ex.info, ex.errT)
      val expressionStmt = transformExp(transformedExp, c)
      Seqn(Seq(inhaleWitnesses, expressionStmt), freshDecls)(ex.pos, ex.info, ex.errT)
    case fa: FuncLikeApp =>
      val argStmts = fa.args.map(transformExp(_, c))
      Seqn(argStmts, Nil)()
    case e: ExtensionExp => reportUnsupportedExp(e)
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
    * Turns `vars` into new local variable declarations with a unique name and replaces their occurrences in `exp`.
    * The new local variables declarations and the transformed expression are returned
    */
  protected def substituteWithFreshVars(vars: Seq[LocalVarDecl], exp: Exp): (Seq[LocalVarDecl], Exp, Seq[(LocalVarDecl, String)]) = {
    val declMapping = vars.map(decl => decl -> uniqueName(decl.name))
    val freshDecls = declMapping.map {
      case (oldDecl, freshName) => LocalVarDecl(freshName, oldDecl.typ)(oldDecl.pos, oldDecl.info, oldDecl.errT)
    }
    val transformedExp = substituteVars(declMapping, exp)
    (freshDecls, transformedExp, declMapping)
  }

  protected def substituteVars[T <: Node](varMapping: Seq[(LocalVarDecl, String)], n: T): T = {
    n.transform({
      case v@LocalVar(name, typ) => varMapping
        // check whether the local variable is in the map of variables that should be replaced:
        .collectFirst { case (decl, freshName) if decl.name == name => freshName }
        // replace it by a new local variable:
        .map(freshName => LocalVar(freshName, typ)(v.pos, v.info, v.errT))
        // keep the variable unchanged if no replacement should happen:
        .getOrElse(v)
    }, Traverse.TopDown)
  }

  /**
   * The simplifyStmts Strategy can be used to simplify statements
   * by e.g. removing or combining nested Seqn or If clauses.
   * This is in particular useful for the expression to statement transformer
   * because this often creates nested and empty Seqn and If clauses.
   *
   * This is a repeating strategy because the removal of unneccessary unfold/fold statements requires EmptyStmts
   * to be removed beforehand. Therefore, it should only be used with an maximum number of iterations (2).
   *
   */
  val simplifyStmts: RepeatedStrategy[Node] = ViperStrategy.Slim({
    case Seqn(EmptyStmt, _) => // remove empty Seqn (including unnecessary scopedDecls)
      EmptyStmt
    case s@Seqn(Seq(Seqn(ss, scopedDecls2)), scopedDecls1) => // combine nested Seqn
      Seqn(ss, scopedDecls1 ++ scopedDecls2)(s.pos, s.info, s.errT)
    case s@Seqn(ss, scopedDecls) if ss.contains(EmptyStmt) => // remove empty statements
      val newSS = ss.filterNot(_ == EmptyStmt)
      Seqn(newSS, scopedDecls)(s.pos, s.info, s.errT)
    case Seqn(Seq(Unfold(acc1), Fold(acc2)), _) if acc1 == acc2 => // remove unfold/fold with nothing in between
      EmptyStmt
    case If(_, EmptyStmt, EmptyStmt) => // remove empty If clause
      EmptyStmt
    case i@If(c, EmptyStmt, els) => // change If with only els to If with only thn
      If(Not(c)(c.pos), els, EmptyStmt)(i.pos, i.info, i.errT)
    case i@If(c1, Seqn(Seq(If(c2, thn, EmptyStmt)), Nil), EmptyStmt) => // combine nested if clauses
      If(And(c1, c2)(), thn, EmptyStmt)(i.pos, i.info, i.errT)
    case If(TrueLit(), thn, _) => thn // remove trivial If conditions (in particular effective together with the next 2 simplifications)
    case And(TrueLit(), rhs) => rhs // simplify conjunctions
    case And(lhs, TrueLit()) => lhs // simplify conjunctions
  }, Traverse.BottomUp)
    .repeat
}

trait ExpressionContext {
  val conditionInEx: Option[LocalVarDecl]
}