// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion

/**
  * Viper to Viper translation of impure assume statements into pure assumes:
  *   an assume of the form assume acc(x.f, p) && acc(y.f, p) is transformed into
  *   perm(x.f) >= p && perm(y.f) >= assume_helper_0(x == y, p, p), where assume_helper_0 is a domain function
  *   of an added domain for assume statements. The function is a conditional sum of permissions, where the condition is
  *   the first argument: assume_helper_0(x == y, p, p) == p + (x == y ? p : none)
  *
  *   if there are more conjunctions, additional functions are generated to check aliasing
  */

object AssumeRewriter {
  val domainName = "Assume"

  var funcs: Seq[DomainFunc] = Seq()
  var axioms: Seq[DomainAxiom] = Seq()
  var inverses = Seq.empty[DomainFunc]
  var domains = Seq.empty[Domain]

  def rewrite(exp: Exp, program: Program) : Exp = {

    /**
      * Rewrites assume statements:
      *   assume statements are rewritten using
      * Context: Pair of condition and variable to replace in the condition as well as the
      * permission amount
      */

    val strat = ViperStrategy.Context[Map[Resource, Seq[((Exp, Seq[Exp]), Exp)]]]({
      case (fap: FieldAccessPredicate, c) =>
        val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
        val dummyVar = LocalVar("dummy", Ref)()
        val ctx = c.updateContext(c.c + (fap.loc.field -> (c.c.getOrElse(fap.loc.field, Seq()) :+ ((EqCmp(fap.loc.rcv, dummyVar)(fap.pos, fap.info, fap.errT), Seq(dummyVar)), fap.perm))))
        if (!insideWand) {
          val cp = CurrentPerm(fap.loc)(fap.pos, fap.info, fap.errT)
          val p = generatePermUsingFunc(c.c.getOrElse(fap.loc.field, Seq()), Seq(fap.loc.rcv), fap.perm, cp, None)
          (p, ctx)
        } else {
          (fap, ctx)
        }
      case (pred: PredicateAccessPredicate, c) =>
        val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
        val dummyVars = (Stream.from(0) map (i => LocalVar("dummy" + i, pred.loc.loc(program).formalArgs(i).typ)())) take pred.loc.args.length
        val eqs = (pred.loc.args zip dummyVars) map (a => EqCmp(a._1, a._2)())
        val cond = eqs.tail.foldLeft[Exp](eqs.head)((a, e) => And(a,e)())
        val ctx = c.updateContext(c.c + (pred.loc.loc(program) -> (c.c.getOrElse(pred.loc.loc(program), Seq()) :+ ((cond, dummyVars), pred.perm))))
        if (!insideWand && (if (c.parentOption.isDefined) !c.parent.isInstanceOf[Unfolding] else true)) {
          val cp = CurrentPerm(pred.loc)(pred.pos, pred.info, pred.errT)
          val p = generatePermUsingFunc(c.c.getOrElse(pred.loc.loc(program), Seq()), pred.loc.args, pred.perm, cp, None)
          (p, ctx)
        } else {
          (pred, ctx)
        }
      case (wand: MagicWand, c) =>
        val dummyVars = (Stream.from(0) map (i => LocalVar("dummy" + i, wand.structure(program).subexpressionsToEvaluate(program)(i).typ)())) take wand.subexpressionsToEvaluate(program).length
        val eqs = (wand.subexpressionsToEvaluate(program) zip dummyVars) map (a => EqCmp(a._1, a._2)())
        val cond = eqs.tail.foldLeft[Exp](eqs.head)((a, e) => And(a,e)())
        val ctx = c.updateContext(c.c + (wand.structure(program) -> (c.c.getOrElse(wand.structure(program), Seq()) :+ ((cond, dummyVars), FullPerm()()))))
        if (!c.parent.isInstanceOf[CurrentPerm] && !c.parent.isInstanceOf[Trigger] && !c.parent.isInstanceOf[Applying]) {
          val cp = CurrentPerm(wand)(wand.pos, wand.info, wand.errT)
          val p = generatePermUsingFunc(c.c.getOrElse(wand.structure(program), Seq()), wand.subexpressionsToEvaluate(program), FullPerm()(), cp, None)
          (p, ctx)
        } else {
          (wand, ctx)
        }
      case (and: And, c) =>
        val lupdate = update(and.left, program)
        val newC = lupdate map (lu => {
          val update = c.c.getOrElse(lu._1, Seq())
          (lu._1, lu._2 ++ update)
        })
        (and, c.updateContext(c.c ++ newC))
      case (QuantifiedPermissionAssertion(forall, cond, acc), c) =>
        acc match {
          case fap: FieldAccessPredicate =>
            val ctx = c.updateContext(c.c + (fap.loc.field -> (c.c.getOrElse(fap.loc.field, Seq()) :+ ((cond, forall.variables map (_.localVar)), fap.perm))))
            val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
            if (!insideWand) {
              val cp = CurrentPerm(fap.loc)(fap.pos, fap.info, fap.errT)
              val p = generatePermUsingFunc(c.c.getOrElse(fap.loc.field, Seq()), Seq(fap.loc.rcv), fap.perm, cp, Some(cond))
              (forall.replace(acc, p), ctx)
            } else {
              (forall, ctx)
            }
          case pred: PredicateAccessPredicate =>
            val ctx = c.updateContext(c.c + (pred.loc.loc(program) -> (c.c.getOrElse(pred.loc.loc(program), Seq()) :+ ((cond, forall.variables map (_.localVar)), pred.perm))))
            val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
            if (!insideWand) {
              val cp = CurrentPerm(pred.loc)(pred.pos, pred.info, pred.errT)
              val p = generatePermUsingFunc(c.c.getOrElse(pred.loc.loc(program), Seq()), pred.loc.args, pred.perm, cp, Some(cond))
              (forall.replace(acc, p), ctx)
            } else {
              (forall, ctx)
            }
          case wand: MagicWand =>
            val ctx = c.updateContext(c.c + (wand.structure(program) -> (c.c.getOrElse(wand.structure(program), Seq()) :+ ((cond, forall.variables map (_.localVar)), FullPerm()()))))
            if (!c.parent.isInstanceOf[CurrentPerm]) {
              val cp = CurrentPerm(wand)(wand.pos, wand.info, wand.errT)
              val p = generatePermUsingFunc(c.c.getOrElse(wand.structure(program), Seq()), wand.subexpressionsToEvaluate(program), FullPerm()(), cp, Some(cond))
              (forall.replace(acc, p), ctx)
            } else {
              (forall, ctx)
            }
        }
    }, Map(): Map[Resource, Seq[((Exp, Seq[Exp]), Exp)]])

    strat.execute(exp)
  }

  /**
    * Creates context updates for the lhs of a conjunction which need to be passed down to the rhs
    * @param node lhs of conjunction for which we update the context
    * @param program current program that is being rewritten
    * @return context update for the above rewriter
    */
  def update(node: Node, program: Program): Seq[(Resource, Seq[((Exp, Seq[Exp]), Exp)])] = {
    node match {
      case fp: FieldAccessPredicate =>
        val dummyVar = LocalVar("dummy", Ref)()
        Seq(fp.loc.field -> Seq(((EqCmp(fp.loc.rcv, dummyVar)(fp.pos, fp.info, fp.errT), Seq(dummyVar)), fp.perm)))
      case pred: PredicateAccessPredicate =>
        val dummyVars = (Stream.from(0) map (i => LocalVar("dummy" + i, pred.loc.loc(program).formalArgs(i).typ)())) take pred.loc.args.length
        val eqs = (pred.loc.args zip dummyVars) map (a => EqCmp(a._1, a._2)())
        val cond = eqs.tail.foldLeft[Exp](eqs.head)((a, e) => And(a,e)())
        Seq(pred.loc.loc(program) -> Seq(((cond, dummyVars), pred.perm)))
      case wand: MagicWand =>
        val dummyVars = (Stream.from(0) map (i => LocalVar("dummy" + i, wand.structure(program).subexpressionsToEvaluate(program)(i).typ)())) take wand.subexpressionsToEvaluate(program).length
        val eqs = (wand.subexpressionsToEvaluate(program) zip dummyVars) map (a => EqCmp(a._1, a._2)())
        val cond = eqs.tail.foldLeft[Exp](eqs.head)((a, e) => And(a,e)())
        Seq(wand.structure(program) -> Seq(((cond, dummyVars), FullPerm()())))
      case QuantifiedPermissionAssertion(forall, cond, acc) =>
        acc match {
          case fap: FieldAccessPredicate =>
            Seq(fap.loc.field -> Seq(((cond, forall.variables map (_.localVar)), fap.perm)))
          case pred: PredicateAccessPredicate =>
            Seq(pred.loc.loc(program) -> Seq(((cond, forall.variables map (_.localVar)), pred.perm)))
          case wand: MagicWand =>
            Seq(wand.structure(program) -> Seq(((cond, forall.variables map (_.localVar)), FullPerm()())))
        }
      case _: Trigger | _: CurrentPerm | _: Unfolding | _: Applying=> Seq()
      case n =>
        val subUpdate = n.subnodes flatMap (sub => update(sub, program))
        subUpdate.groupBy(_._1).map{ case (k,v) => (k, v.flatMap(_._2))}.toSeq
    }
  }

  def rewriteInhale(inhale: Inhale) : Stmt = {

    var seq: Seq[Inhale] = Seq()
    val exps = inhale.exp match {
      case and: And => split(and)
      case other => Seq(other)
    }

    for (e <- exps) {
      seq = seq :+ Inhale(e)(e.pos, e.info, e.errT)
    }

    val seqn = Seqn(seq, Seq())(inhale.pos, inhale.info, inhale.errT)
    seqn
  }

  /**
    * Generates the rewritten perm expressions using domain functions. The expressions are of the form perm(res) >= func
    * with func being a helper function. Which helper function to use depends on the size of the conjunction to rewrite,
    * the bigger the conjuction, the more possibilities for aliasing there are.
    *
    * @param context context from the rewriter for the current resource
    * @param rcv arguments of the resource for the expression that is currently being rewritten
    * @param perm permission amount added to the resource by the expression that is being rewritten
    * @param permLoc perm expression for the rewritten expression
    * @param cond condition used by QPs to determine if a given QP assertion provides permission to some location
    * @return rewritten perm expression that replaces the impure assume statement
    */
  def generatePermUsingFunc(context: Seq[((Exp, Seq[Exp]), Exp)], rcv: Seq[Exp], perm: Exp, permLoc: CurrentPerm, cond: Option[Exp]): Exp = {

    assert(context.forall(c => c._1._2.length == rcv.length))

    val contextWithoutRcv = cond match {
      case Some(exp) =>
        context.filter(c => !c._1._1.equals(exp))
      case None =>
        context.filter(c => !rcv.forall(e => c._1._1.contains(e)))
    }
    if (contextWithoutRcv.isEmpty) return PermGeCmp(permLoc, perm)()

    val conds = contextWithoutRcv map (c => c._1._1.replace((c._1._2 zip rcv).toMap[Exp, Exp]))
    val perms = (contextWithoutRcv map (_._2)) :+ perm

    if (funcs.length <= contextWithoutRcv.length-1) {
      val (fun, ax) = generateFunc(funcs.length + 1)
      funcs = funcs :+ fun
      axioms = axioms :+ ax
    }

    val func = funcs(contextWithoutRcv.length-1)
    val funcApp = DomainFuncApp(func, conds ++ perms, Map[TypeVar, Type]())()
    PermGeCmp(permLoc, funcApp)()
  }

  def split(exp: Exp): Seq[Exp] = {
    exp match {
      case and: And => split(and.left) ++ split(and.right)
      case other => Seq(other)
    }
  }

  /**
    * Generates the helper functions used to rewrite the assume statements.
    * Every helper function is of the form p + (c1 ? p1 : none) + (c2 ? p2 : none) + ...
    * The size of the helper function (i.e. how many conditional sums there are) depends on the size of an assumed conjunction
    * that is being rewritten.
    *
    * @param numOfConds number of conditional sums in this helper function
    * @return The new domain function as well as the axiom defining the value of the function
    */
  def generateFunc(numOfConds: Int): (DomainFunc, DomainAxiom) = {
    val name = "assume_helper_" + numOfConds
    var conds: Seq[LocalVar] = Seq()
    var perms: Seq[LocalVar] = Seq()
    var cDecls: Seq[LocalVarDecl] = Seq()
    var pDecls: Seq[LocalVarDecl] = Seq(LocalVarDecl("p_0", Perm)())
    val formalArgs = {
      for (i <- 0 until numOfConds) {
        cDecls = LocalVarDecl("c_" + (i+1), Bool)() +: cDecls
        if (i < numOfConds) conds = conds :+ LocalVar("c_" + (i+1), Bool)()
      }
      for (i <- 0 until numOfConds) {
        pDecls = LocalVarDecl("p_" + (i+1), Perm)() +: pDecls
        if (i < numOfConds) perms = perms :+ LocalVar("p_" + (i+1), Perm)()
      }
      cDecls ++ pDecls
    }
    val body = {
      val condsWithPerm = conds zip perms

      val condExps = condsWithPerm map (cp => CondExp(cp._1, cp._2, NoPerm()())())
      condExps.foldLeft[Exp](LocalVar("p_0", Perm)())((p, c) => PermAdd(p, c)())
    }
    val fun = DomainFunc(name, formalArgs, Perm)(domainName = domainName)
    val ax = Forall(formalArgs, Seq(Trigger(Seq(DomainFuncApp(fun, formalArgs map (_.localVar), Map[TypeVar, Type]())()))()), EqCmp(DomainFuncApp(fun, formalArgs map (_.localVar), Map[TypeVar, Type]())(), body)())()
    val dax = NamedDomainAxiom(name + "_axiom", ax)(domainName = domainName)
    (fun, dax)
  }

  def rewriteQPs(exp: Exp, program: Program): Exp = {
    exp match {
      case forall: Forall =>
        val invForall = InverseFunctions.getFreshInverse(forall, program)
        invForall match {
          case (Some((invs, domain)), Some(axs), forall1) =>
            inverses ++= invs
            domains :+= domain
            val ax = axs.tail.foldLeft[Exp](axs.head)((e, f) => And(e, f)())
            And(ax, forall1)()
          case _ => forall
        }
      case _ => exp.replace((exp.subExps zip (exp.subExps map (e => rewriteQPs(e, program)))).toMap)
    }
  }

  /**
    * Rewrites assumes in 3 stages: first transforms all QPs using inverse functions,
    * secondly transforms all the assumes using the generated helper functions,
    * then adds the used functions to the program
    */

  def rewriteAssumes(p: Program): Program = {

    funcs = Seq.empty
    axioms = Seq.empty
    inverses = Seq.empty
    domains = Seq.empty

    val pInvs: Program = ViperStrategy.Slim({
      case a: Assume => a.replace(a.exp, rewriteQPs(a.exp, p))
    }).execute(p)

    val pAssume: Program = ViperStrategy.Slim({
      case a: Assume => rewriteInhale(Inhale(rewrite(a.exp, pInvs))(a.pos))
    }).execute(pInvs)

    if (funcs.isEmpty && domains.isEmpty) {
      pAssume
    } else {
      ViperStrategy.Slim({
        case p: Program if funcs.nonEmpty =>
          val assumeDomain = Domain(domainName, funcs, axioms)(info = Synthesized)

          Program(p.domains ++ domains :+ assumeDomain, p.fields, p.functions, p.predicates, p.methods, p.extensions)(p.pos, p.info, p.errT)
      }).execute(pAssume)
    }
  }
}
