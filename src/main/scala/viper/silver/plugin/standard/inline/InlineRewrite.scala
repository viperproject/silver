package viper.silver.plugin.standard.inline

import viper.silver.ast.{Exp, Fold, LocalVar, Method, PredicateAccess, Program, Stmt, Unfold}

trait InlineRewrite {

  def inlinePredicates(method: Method, program: Program): Method = {
    val expandedPres = method.pres.map { pre =>
      expandPredicate(pre, program).fold(pre)(expandedPred => expandedPred)
    }
    val expandedPosts = method.posts.map { post =>
      expandPredicate(post, program).fold(post)(expandedPred => expandedPred)
    }
    method.copy(name = method.name,
      formalArgs = method.formalArgs,
      formalReturns = method.formalReturns,
      pres = expandedPres,
      posts = expandedPosts,
      body = method.body
    )(pos = method.pos, info = method.info, errT = method.errT)
  }

  def removeUnfoldFold(method: Method, program: Program): Method = {
    val expandablePredicateIds = getExpandablePredicateIds(method.pres, program)
    val rewrittenBody = method.body.map { body =>
      val bodyWithRemovedUnfolds = removeUnfolds(body.ss, expandablePredicateIds)
      val bodyWithRemovedUnfoldFolds = removeFolds(bodyWithRemovedUnfolds, expandablePredicateIds)
      body.copy(ss = bodyWithRemovedUnfoldFolds, scopedDecls = body.scopedDecls)(
        pos = body.pos, info = body.info, errT = body.errT
      )
    }
    method.copy(name = method.name,
      formalArgs = method.formalArgs,
      formalReturns = method.formalReturns,
      pres = method.pres,
      posts = method.posts,
      body = rewrittenBody
    )(pos = method.pos, info = method.info, errT = method.errT)
  }

  private[this] def expandPredicate(expr: Exp, program: Program): Option[Exp] =
    expr match {
      case pred: PredicateAccess => getPredicateBody(pred, program)
      case _ => None
    }

  private[this] def getPredicateBody(pred: PredicateAccess, program: Program): Option[Exp] = {
    def extractLocalVarIds(predicate: PredicateAccess): Set[String] =
      predicate.args.map {
        case arg: LocalVar => arg.name
        case _ => ""
      }.filter(_.nonEmpty).toSet

    val args = extractLocalVarIds(pred)
    pred.predicateBody(program, args)
  }

  private[this] def getExpandablePredicateIds(exprs: Seq[Exp], program: Program): Seq[String] =
    exprs.collect {
      case exp: PredicateAccess if getPredicateBody(exp, program).nonEmpty => exp.predicateName
  }

  private[this] def removeUnfolds(bodyStmts: Seq[Stmt], predicatesToRemove: Seq[String]): Seq[Stmt] =
    bodyStmts.filter {
      case unfoldExp: Unfold =>
        val unfoldPredName = unfoldExp.acc.loc.predicateName
        predicatesToRemove.contains(unfoldPredName)
      case _ => false
    }

  private[this] def removeFolds(bodyStmts: Seq[Stmt], predicatesToRemove: Seq[String]): Seq[Stmt] = {
    bodyStmts.filter {
      case foldExp: Fold =>
        val foldPredName = foldExp.acc.loc.predicateName
        predicatesToRemove.contains(foldPredName)
      case _ => false
    }
  }
}
