package viper.silver.plugin.standard.inline

import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse

trait InlineRewrite extends PredicateExpansion with InlineErrorChecker {

  def rewriteMethod(method: Method, program: Program, cond: String => Boolean): Method = {
    val expandedPres = method.pres.map(expandExpression(_, method, program, cond))
    val expandedPosts = method.posts.map(expandExpression(_, method, program, cond))
    val rewrittenBody = method.body.map(expandStatements(_, method, program, cond))
    method.copy(body = rewrittenBody,
      pres = expandedPres,
      posts = expandedPosts
    )(method.pos, method.info, method.errT)
  }

  def rewriteFunction(function: Function, program: Program, cond: String => Boolean): Function = {
    val expandedPres = function.pres.map(expandExpression(_, function, program, cond))
    val expandedPosts = function.posts.map(expandExpression(_, function, program, cond))
    val rewrittenBody = function.body.map(expandExpression(_, function, program, cond))
    function.copy(body = rewrittenBody,
      pres = expandedPres,
      posts = expandedPosts
    )(function.pos, function.info, function.errT)
  }

  def rewritePredicate(pred: Predicate, program: Program, cond: String => Boolean): Predicate = {
    val rewrittenBody = pred.body.map(expandExpression(_, pred, program, cond))
    pred.copy(body = rewrittenBody,
    )(pred.pos, pred.info, pred.errT)
  }

  def unfolding_name(name: String): String = f"__unfolding_${name}__"

  /**
   * Transforms a predicate into a function that requires the predicates body and can be used in unfolding
   */
  def transformPredicate(pred: Predicate, program: Program, cond: String => Boolean): Function = {
    val rewrittenBody = pred.body.map(expandExpression(_, pred, program, cond))
    val name = unfolding_name(pred.name)
    Function(name, pred.formalArgs, Bool, Seq(rewrittenBody.get), Seq(), Some(TrueLit()()))(pred.pos, pred.info, pred.errT)
  }

  /**
    * Expands all predicates to their bodies in given expression.
    *
    * @param expr The expression whose predicates will be expanded.
    * @param member The member containing the expression, used to determine locally-scoped variables.
    * @param program The program containing the expression, used to expand predicates.
    * @param cond The predicate (Scala) that the predicates (Viper) must satisfy.
    * @return The expression with expanded predicates and the expandable precondition and postcondition predicates.
    */
  private[this] def expandExpression(expr: Exp, member: Member, program: Program, cond: String => Boolean, decls: Set[String] = Set()): Exp = {
    val noUnfoldingExpr = removeUnfoldings(expr, cond)
    ViperStrategy.CustomContext[Set[String]]({
      case (expr@PredicateAccessPredicate(pred, perm), ctxt) =>
        if (cond(pred.predicateName)) {
          val optPredBody = propagatePermission(pred.predicateBody(program, ctxt), perm)
          val expandedExpr = expandExpression(optPredBody.get, member, program, cond)
          val res = And(PermGeCmp(perm, NoPerm()())(), Implies(PermGtCmp(perm, NoPerm()())(), expandedExpr)())()
          (res, ctxt)
        } else (expr, ctxt)
      case (scope: Scope, ctxt) =>
        (scope, ctxt ++ scope.scopedDecls.map(_.name).toSet)
    }, member.scopedDecls.map(_.name).toSet ++ decls, Traverse.TopDown).execute[Exp](noUnfoldingExpr)
  }

  /**
    * Given an inhale, exhale, or assert statement, or a while loop invariant,
    * look within it for any predicate accesses.
    * If found, return the same statement with the expanded body of the predicate.
    *
    * @param stmts A Seqn whose statements will be traversed.
    * @param member The member containing the inhale statement we wish to expand.
    * @param program The Viper program for which we perform this expansion.
    * @param cond The condition a predicate must satisfy to be expanded within an inhale statement.
    * @return The Seqn with all inhale, exhale, assert, and while loop statements expanded.
    */
  private[this] def expandStatements(stmts: Seqn, member: Member, program: Program, cond: String => Boolean): Seqn = {
    val noFoldUnfoldStmts = removeFoldUnfolds(stmts, member, program, cond)
    ViperStrategy.CustomContext[Set[String]]({
      case (inhale@Inhale(expr), ctxt) =>
        val expandedExpr = expandExpression(expr, member, program, cond, ctxt)
        (inhale.copy(expandedExpr)(pos = inhale.pos, info = inhale.info, errT = inhale.errT), ctxt)
      case (exhale@Exhale(expr), ctxt) =>
        val expandedExpr = expandExpression(expr, member, program, cond, ctxt)
        (exhale.copy(expandedExpr)(pos = exhale.pos, info = exhale.info, errT = exhale.errT), ctxt)
      case (assert@Assert(expr), ctxt) =>
        val expandedExpr = expandExpression(expr, member, program, cond, ctxt)
        (assert.copy(expandedExpr)(pos = assert.pos, info = assert.info, errT = assert.errT), ctxt)
      case (loop@While(_, invs, _), ctxt) =>
        val expandedInvs = invs.map(expandExpression(_, member, program, cond, ctxt))
        (loop.copy(invs = expandedInvs)(pos = loop.pos, info = loop.info, errT = loop.errT), ctxt)
      case (seqn@Seqn(_, scopedDecls), ctxt) =>
        (seqn, ctxt ++ scopedDecls.map(_.name))
      case (expr: Exp, ctxt) => (removeUnfoldings(expr, cond), ctxt)
    }, stmts.scopedDecls.map(_.name).toSet, Traverse.TopDown).execute[Seqn](noFoldUnfoldStmts)
  }

  /**
    * Replaces unfolding expressions by their bodies if the unfolded predicate had been expanded
    *
    * @param expr The expression whose unfoldings may be substituted.
    * @param cond The condition a predicate must satisfy to be un-unfolding-ed.
    * @return The expression with unfoldings possibly substituted.
    */
  private[this] def removeUnfoldings(expr: Exp, cond: String => Boolean): Exp = {
    ViperStrategy.Slim({
      case unfolding@Unfolding(PredicateAccessPredicate(PredicateAccess(args, name), _), body) =>
        if (cond(name)) {
          val unfolding_check = FuncApp(unfolding_name(name), args)(unfolding.pos, unfolding.info, Bool, unfolding.errT)
          DomainFuncApp(secondDomain.functions.head, Seq(unfolding_check, body), Map((secondDomain.typVars.head, body.typ)))(unfolding.pos, unfolding.info, unfolding.errT)
        } else unfolding
    }, Traverse.BottomUp).execute[Exp](expr)
  }

  val secondDomain: Domain = {
    val name = "__SECOND__"
    val tv = TypeVar("T")
    val args = Seq(LocalVarDecl("b", Bool)(), LocalVarDecl("t", tv)())
    val func = DomainFunc("__second__", args, tv)(domainName = name)
    val app = DomainFuncApp(func=func, args.map(_.localVar), Map((tv, tv)))()
    val ax = AnonymousDomainAxiom(Forall(args, Seq(Trigger(Seq(app))()), EqCmp(app, args(1).localVar)())())(domainName = name)
    Domain(name, Seq(func), Seq(ax), Seq(tv))()
  }

  /**
    * Transforms predicate unfolds and folds into assertions.
    *
    * @param stmts A Seqn whose statements will be traversed.
    * @param cond The condition a predicate must satisfy to no longer require (un)folding.
    * @return The Seqn with all possible unfolds and folds turned into assertions.
    */
  private[this] def removeFoldUnfolds(stmts: Seqn, member: Member, program: Program, cond: String => Boolean): Seqn = {
    ViperStrategy.CustomContext[Set[String]]({
      case (fold@Fold(PredicateAccessPredicate(pred, perm)), ctxt) =>
        if (cond(pred.predicateName)) {
          val optPredbody = propagatePermission(pred.predicateBody(program, ctxt), perm)
          (Assert(optPredbody.get)(fold.pos, fold.info, fold.errT), ctxt)
        } else (fold, ctxt)
      case (unfold@Unfold(PredicateAccessPredicate(pred, perm)), ctxt) =>
        if (cond(pred.predicateName)) {
          val optPredbody = propagatePermission(pred.predicateBody(program, ctxt), perm)
          val res = And(PermGtCmp(perm, NoPerm()())(), optPredbody.get)()
          (Assert(res)(unfold.pos, unfold.info, unfold.errT), ctxt)
        } else (unfold, ctxt)
    }, member.scopedDecls.map(_.name).toSet, Traverse.BottomUp).execute[Seqn](stmts)
  }
}
