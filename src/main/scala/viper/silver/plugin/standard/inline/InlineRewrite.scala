package viper.silver.plugin.standard.inline

import viper.silver.ast.{ErrTrafo, _}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.verifier.{AbstractVerificationError, ErrorMessage, ErrorReason, errors}
import viper.silver.verifier.errors.{AssertFailed, AssignmentFailed, CallFailed, ContractNotWellformed, ExhaleFailed, FoldFailed, FunctionNotWellformed, InhaleFailed, PreconditionInAppFalse, PredicateNotWellformed, UnfoldFailed, WhileFailed}
import viper.silver.verifier.reasons.{AssertionFalse, InsufficientPermission, NegativePermission}

trait InlineRewrite extends PredicateExpansion with InlineErrorChecker {

  def contract_err_type(c: Exp): ErrorReason => ContractNotWellformed = (r: ErrorReason) => ContractNotWellformed(c, r)

  def rewriteMethod(method: Method, program: Program, cond: String => Boolean): Method = {
    val expandedPres = method.pres.map({ c => expandExpression(c, method, program, cond, err_type = contract_err_type(c)) })
    val expandedPosts = method.posts.map({ c => expandExpression(c, method, program, cond, err_type = contract_err_type(c)) })
    val rewrittenBody = method.body.map(expandStatements(_, method, program, cond))
    method.copy(body = rewrittenBody,
      pres = expandedPres,
      posts = expandedPosts
    )(method.pos, method.info, method.errT)
  }

  def rewriteFunction(function: Function, program: Program, cond: String => Boolean): Function = {
    val err_type = (r: ErrorReason) => FunctionNotWellformed(function, r)
    val expandedPres = function.pres.map({ c => expandExpression(c, function, program, cond, contract_err_type(c)) })
    val expandedPosts = function.posts.map({ c => expandExpression(c, function, program, cond, contract_err_type(c)) })
    val rewrittenBody = function.body.map((expr: Exp) => expandExpression(expr, function, program, cond, err_type))
    function.copy(body = rewrittenBody,
      pres = expandedPres,
      posts = expandedPosts
    )(function.pos, function.info, function.errT)
  }

  def rewritePredicate(pred: Predicate, program: Program, cond: String => Boolean): Predicate = {
    val err_type = (r: ErrorReason) => PredicateNotWellformed(pred, r)
    val rewrittenBody = pred.body.map((expr: Exp) => expandExpression(expr, pred, program, cond, err_type))
    pred.copy(body = rewrittenBody,
    )(pred.pos, pred.info, pred.errT)
  }

  def unfolding_name(name: String): String = f"__unfolding_${name}__"

  /**
   * Transforms a predicate into a function that requires the predicates body and can be used in unfolding
   */
  def transformPredicate(pred: Predicate, program: Program, cond: String => Boolean): Function = {
    val err_type = (r: ErrorReason) => PredicateNotWellformed(pred, r)
    val permDecl = LocalVarDecl("__perm__", Perm)()
    val permVar = LocalVar("__perm__", Perm)()
    val rewrittenBody = propagatePermission(pred.body, permVar).get
    val expandedBody = expandExpression(rewrittenBody, pred, program, cond, err_type)
    val name = unfolding_name(pred.name)
    Function(name, pred.formalArgs ++ Seq(permDecl), Bool, Seq(wrapPred(expandedBody, permVar)), Seq(), Some(TrueLit()()))(pred.pos, pred.info, pred.errT)
  }

  def wrapPred(expandedExpr: Exp, perm: Exp): Exp = And(PermGeCmp(perm, NoPerm()())(), Implies(PermGtCmp(perm, NoPerm()())(), expandedExpr)())()
  /**
   * Expands all predicates to their bodies in given expression.
   *
   * @param expr     The expression whose predicates will be expanded.
   * @param member   The member containing the expression, used to determine locally-scoped variables.
   * @param program  The program containing the expression, used to expand predicates.
   * @param cond     The predicate (Scala) that the predicates (Viper) must satisfy.
   * @param err_type A function that generates a relevant error given an error unfolding
   * @return The expression with expanded predicates and the expandable precondition and postcondition predicates.
   */
  private def expandExpression(expr: Exp, member: Member, program: Program, cond: String => Boolean, err_type: ErrorReason => AbstractVerificationError, decls: Set[String] = Set()): Exp = {
    val noUnfoldingExpr = removeUnfoldings(expr, cond, err_type)
    ViperStrategy.CustomContext[Set[String]]({
      case (expr@PredicateAccessPredicate(pred, perm), ctxt) =>
        if (cond(pred.predicateName)) {
          val optPredBody = propagatePermission(pred.predicateBody(program, ctxt), perm)
          val expandedExpr = expandExpression(optPredBody.get, member, program, cond, err_type)
          val res = wrapPred(expandedExpr, perm)
          (res, ctxt)
        } else (expr, ctxt)
      case (scope: Scope, ctxt) =>
        (scope, ctxt ++ scope.scopedDecls.map(_.name).toSet)
    }, member.scopedDecls.map(_.name).toSet ++ decls, Traverse.TopDown).execute[Exp](noUnfoldingExpr)
  }

  case class UnknownUnfoldingError(offendingNode: Exp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
    val id = "unknown.unfolding.failed"
    val text = s"Unknown unfolding error"

    def withNode(offendingNode: errors.ErrorNode = this.offendingNode): ErrorMessage = UnknownUnfoldingError(offendingNode.asInstanceOf[Exp], this.reason, this.cached)

    def withReason(r: ErrorReason): AbstractVerificationError = UnknownUnfoldingError(offendingNode, r, cached)
  }

  /**
   * Given an inhale, exhale, or assert statement, or a while loop invariant,
   * look within it for any predicate accesses.
   * If found, return the same statement with the expanded body of the predicate.
   *
   * @param stmts   A Seqn whose statements will be traversed.
   * @param member  The member containing the inhale statement we wish to expand.
   * @param program The Viper program for which we perform this expansion.
   * @param cond    The condition a predicate must satisfy to be expanded within an inhale statement.
   * @return The Seqn with all inhale, exhale, assert, and while loop statements expanded.
   */
  private[this] def expandStatements(stmts: Seqn, member: Member, program: Program, cond: String => Boolean): Seqn = {
    val noFoldUnfoldStmts = removeFoldUnfolds(stmts, member, program, cond)
    ViperStrategy.CustomContext[Set[String]]({
      case (inhale@Inhale(expr), ctxt) =>
        val err_type = (r: ErrorReason) => InhaleFailed(inhale, r)
        val expandedExpr = expandExpression(expr, member, program, cond, err_type, ctxt)
        (inhale.copy(expandedExpr)(pos = inhale.pos, info = inhale.info, errT = inhale.errT), ctxt)
      case (exhale@Exhale(expr), ctxt) =>
        val err_type = (r: ErrorReason) => ExhaleFailed(exhale, r)
        val expandedExpr = expandExpression(expr, member, program, cond, err_type, ctxt)
        (exhale.copy(expandedExpr)(pos = exhale.pos, info = exhale.info, errT = exhale.errT), ctxt)
      case (assert@Assert(expr), ctxt) =>
        val err_type = (r: ErrorReason) => AssertFailed(assert, r)
        val expandedExpr = expandExpression(expr, member, program, cond, err_type, ctxt)
        (assert.copy(expandedExpr)(pos = assert.pos, info = assert.info, errT = assert.errT), ctxt)
      case (assign: AbstractAssign, ctxt) =>
        val err_type = (r: ErrorReason) => AssignmentFailed(assign, r)
        val expandedRhs = expandExpression(assign.rhs, member, program, cond, err_type, ctxt)
        (AbstractAssign.apply(assign.lhs, expandedRhs)(pos = assign.pos, info = assign.info, errT = assign.errT), ctxt)
      case (method@MethodCall(_, args, _), ctxt) =>
        val err_type = (r: ErrorReason) => CallFailed(method, r)
        val expandedArgs = args.map(expandExpression(_, member, program, cond, err_type, ctxt))
        (method.copy(args = expandedArgs)(pos = method.pos, info = method.info, errT = method.errT), ctxt)
      case (loop@While(c, invs, _), ctxt) =>
        val err_type = (r: ErrorReason) => WhileFailed(c, r)
        val expandedCond = expandExpression(c, member, program, cond, err_type)
        val expandedInvs = invs.map(inv => expandExpression(inv, member, program, cond, contract_err_type(inv), ctxt))
        (loop.copy(invs = expandedInvs, cond = expandedCond)(pos = loop.pos, info = loop.info, errT = loop.errT), ctxt)
      case (seqn@Seqn(_, scopedDecls), ctxt) =>
        (seqn, ctxt ++ scopedDecls.map(_.name))
      case (expr: Exp, ctxt) =>
        val err_type = (r: ErrorReason) => UnknownUnfoldingError(expr, r)
        (removeUnfoldings(expr, cond, err_type), ctxt)
    }, stmts.scopedDecls.map(_.name).toSet, Traverse.TopDown).execute[Seqn](noFoldUnfoldStmts)
  }

  /**
   * Replaces unfolding expressions by their bodies if the unfolded predicate had been expanded
   *
   * @param expr The expression whose unfoldings may be substituted.
   * @param cond The condition a predicate must satisfy to be un-unfolding-ed.
   * @param err_type A function that generates a relevant error given an error unfolding
   * @return The expression with unfoldings possibly substituted.
   */
  private[this] def removeUnfoldings(expr: Exp, cond: String => Boolean, err_type: ErrorReason => AbstractVerificationError): Exp = {
    ViperStrategy.Slim({
      case unfolding@Unfolding(PredicateAccessPredicate(pred_access@PredicateAccess(args, name), perm), body) =>
        if (cond(name)) {
          val check_errT = ErrTrafo({
            case PreconditionInAppFalse(_, AssertionFalse(PermGeCmp(perm, NoPerm())), _) => err_type(NegativePermission(perm))
            case PreconditionInAppFalse(_, _, _) => err_type(InsufficientPermission(pred_access))
          })
          val unfolding_check = FuncApp(unfolding_name(name), args ++ Seq(perm))(unfolding.pos, unfolding.info, Bool, check_errT)
          DomainFuncApp(secondDomain.functions.head, Seq(unfolding_check, body), Map((secondDomain.typVars.head, body.typ)))(unfolding.pos, unfolding.info, unfolding.errT)
        } else unfolding
    }, Traverse.BottomUp).execute[Exp](expr)
  }

  val secondDomain: Domain = {
    val name = "__SECOND__"
    val tv = TypeVar("T")
    val args = Seq(LocalVarDecl("b", Bool)(), LocalVarDecl("t", tv)())
    val func = DomainFunc("__second__", args, tv)(domainName = name)
    val app = DomainFuncApp(func = func, args.map(_.localVar), Map((tv, tv)))()
    val ax = AnonymousDomainAxiom(Forall(args, Seq(Trigger(Seq(app))()), EqCmp(app, args(1).localVar)())())(domainName = name)
    Domain(name, Seq(func), Seq(ax), Seq(tv))()
  }

  /**
   * Transforms predicate unfolds and folds into assertions.
   *
   * @param stmts A Seqn whose statements will be traversed.
   * @param cond  The condition a predicate must satisfy to no longer require (un)folding.
   * @return The Seqn with all possible unfolds and folds turned into assertions.
   */
  private[this] def removeFoldUnfolds(stmts: Seqn, member: Member, program: Program, cond: String => Boolean): Seqn = {
    ViperStrategy.CustomContext[Set[String]]({
      case (fold@Fold(PredicateAccessPredicate(pred, perm)), ctxt) =>
        if (cond(pred.predicateName)) {
          val optPredbody = propagatePermission(pred.predicateBody(program, ctxt), perm)
          val errT = ErrTrafo({case AssertFailed(_, _, _) => FoldFailed(fold, InsufficientPermission(pred))})
          (Assert(optPredbody.get)(fold.pos, fold.info, errT), ctxt)
        } else (fold, ctxt)
      case (unfold@Unfold(PredicateAccessPredicate(pred, perm)), ctxt) =>
        if (cond(pred.predicateName)) {
          val optPredbody = propagatePermission(pred.predicateBody(program, ctxt), perm)
          val permExp = PermGtCmp(perm, NoPerm()())()
          val res = And(permExp, optPredbody.get)()
          val errT = ErrTrafo({
            case AssertFailed(_, AssertionFalse(`permExp`), _) => UnfoldFailed(unfold, NegativePermission(perm))
            case AssertFailed(_, _, _) => UnfoldFailed(unfold, InsufficientPermission(pred))
          })
          (Assert(res)(unfold.pos, unfold.info, errT), ctxt)
        } else (unfold, ctxt)
    }, member.scopedDecls.map(_.name).toSet, Traverse.BottomUp).execute[Seqn](stmts)
  }
}
