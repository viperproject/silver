// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import viper.silver.ast.{And, Exp, Stmt, _}
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.{ContextCustom, RepeatedStrategy, Strategy, Traverse}

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

      val stmts = Seq(permCheck, unfold, unfoldBody, fold)
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

      val inhaleEq = Inhale(EqCmp(localVarDecl.localVar, letExp.exp)())()

      val bodyStmt = transformExp(letExp.body, c)

      Seqn(Seq(expressionStmt, inhaleEq, bodyStmt), Seq(localVarDecl))()

    case (b: BinExp, c) =>
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
    case (ase: AnySetExp, c) => ase match {
      case AnySetCardinality(s) => Seqn(Seq(transformExp(s, c)), Nil)(ase.pos)
      case AnySetUnion(l, r) => Seqn(Seq(transformExp(l, c), transformExp(r, c)), Nil)(ase.pos)
      case AnySetIntersection(l, r) => Seqn(Seq(transformExp(l, c), transformExp(r, c)), Nil)(ase.pos)
      case AnySetSubset(l ,r) => Seqn(Seq(transformExp(l, c), transformExp(r, c)), Nil)(ase.pos)
      case AnySetMinus(l, r) => Seqn(Seq(transformExp(l, c), transformExp(r, c)), Nil)(ase.pos)
      case AnySetContains(elem, s) => Seqn(Seq(transformExp(elem, c), transformExp(s, c)), Nil)(ase.pos)
      case MapDomain(base) => Seqn(Seq(transformExp(base, c)), Nil)(ase.pos)
      case MapRange(base) => Seqn(Seq(transformExp(base, c)), Nil)(ase.pos)
      case unsupportedExp => transformUnknownExp(unsupportedExp, c)
    }
    case (st: SetExp, c) => st match {
      // note that AnySetExp are handled above
      case ExplicitSet(elems) => Seqn(elems.map(transformExp(_, c)), Nil)(st.pos)
      case EmptySet(_) => EmptyStmt
      case unsupportedExp => transformUnknownExp(unsupportedExp, c)
    }
    case (ms: MultisetExp, c) => ms match {
      // note that AnySetExp are handled above
      case EmptyMultiset(_) => EmptyStmt
      case ExplicitMultiset(elems) => Seqn(elems.map(transformExp(_, c)), Nil)(ms.pos)
      case unsupportedExp => transformUnknownExp(unsupportedExp, c)
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
      case EmptySeq(_) => EmptyStmt
      case unsupportedExp => transformUnknownExp(unsupportedExp, c)
    }
    case (mp: MapExp, c) => mp match {
      case EmptyMap(_, _) => EmptyStmt
      case ExplicitMap(elems) => Seqn(elems.map(transformExp(_, c)), Nil)(mp.pos)
      case Maplet(key, value) => Seqn(Seq(transformExp(key, c), transformExp(value, c)), Nil)(mp.pos)
      case MapCardinality(base) => Seqn(Seq(transformExp(base, c)), Nil)(mp.pos)
      case MapContains(key, base) => Seqn(Seq(transformExp(key, c), transformExp(base, c)), Nil)(mp.pos)
      case MapLookup(base, key) => Seqn(Seq(transformExp(base, c), transformExp(key, c)), Nil)(mp.pos)
      case MapUpdate(base, key, value) => Seqn(Seq(transformExp(base, c), transformExp(key, c), transformExp(value, c)), Nil)(mp.pos)
    }
    case (u: UnExp, c) => transformExp(u.exp, c)
    case (_: Literal, _) => EmptyStmt
    case (_: AbstractLocalVar, _) => EmptyStmt
    case (_: AbstractConcretePerm, _) => EmptyStmt
    case (_: WildcardPerm, _) => EmptyStmt
    case (_: EpsilonPerm, _) => EmptyStmt
    case (_: LocationAccess, _) => EmptyStmt

    case (ap: AccessPredicate, c) =>
      val check = transformExp(ap.perm, c)

      val inhale = Inhale(ap)(ap.pos)

      Seqn(Seq(check, inhale), Nil)()
    case (fa: Forall, c) =>
      // we turn the quantified variables into local variables with arbitrary value and show that the expression holds
      // for arbitrary values, which is similar to a forall introduction
      val (freshDecls, transformedExp) = substituteWithFreshVars(fa.variables, fa.exp)
      val expressionStmt = transformExp(transformedExp, c)
      Seqn(Seq(expressionStmt), freshDecls)(fa.pos, fa.info, fa.errT)
    case (ex: Exists, c) =>
      // we perform existential elimination by retrieving witnesses for the quantified variables
      val (freshDecls, transformedExp) = substituteWithFreshVars(ex.variables, ex.exp)
      // we can't use an assume statement at this point because the `assume`s have already been rewritten
      // furthermore, Viper only allows pure existentially quantified expressions
      val inhaleWitnesses = Inhale(transformedExp)(ex.pos, ex.info, ex.errT)
      val expressionStmt = transformExp(transformedExp, c)
      Seqn(Seq(inhaleWitnesses, expressionStmt), freshDecls)(ex.pos, ex.info, ex.errT)
    case (fa: FuncLikeApp, c) =>
      val argStmts = fa.args.map(transformExp(_, c))
      Seqn(argStmts, Nil)()
    case (unknownExp, c) =>
      transformUnknownExp(unknownExp, c)
  }

  /**
   * Expression transformer if no default is defined.
   * Calls transformExp on all subExps of e.
   * To change or extend the default transformer for unknown expressions
   * override this method (and possibly combine it with super.transformUnknownExp).
   */
  def transformUnknownExp(e: Exp, c: ExpressionContext): Stmt = {
    val sub = e.subExps.map(transformExp(_, c))
    Seqn(sub, Nil)()
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
  protected def substituteWithFreshVars(vars: Seq[LocalVarDecl], exp: Exp): (Seq[LocalVarDecl], Exp) = {
    val declMapping = vars.map(decl => decl -> uniqueName(decl.name))
    val freshDecls = declMapping.map {
      case (oldDecl, freshName) => LocalVarDecl(freshName, oldDecl.typ)(oldDecl.pos, oldDecl.info, oldDecl.errT)
    }
    val transformedExp = exp.transform({
      case v@LocalVar(name, typ) => declMapping
        // check whether the local variable is in the map of variables that should be replaced:
        .collectFirst { case (decl, freshName) if decl.name == name => freshName }
        // replace it by a new local variable:
        .map(freshName => LocalVar(freshName, typ)(v.pos, v.info, v.errT))
        // keep the variable unchanged if no replacement should happen:
        .getOrElse(v)
    }, Traverse.TopDown)
    (freshDecls, transformedExp)
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