// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast._

/** Viper-to-Viper translation of impure assume statements into pure assumes: an assume of the form
  *     assume acc(x.f, p) && acc(y.f, p)
  * is transformed into
  *     perm(x.f) >= p && perm(y.f) >= assume_helper_0(x == y, p, p)
  * where assume_helper_0 is a domain function of a synthetic domain introduced by this rewriter.
  * The function is a conditional sum of permissions, where the condition is the first argument:
  *     assume_helper_0(x == y, p, p) == p + (x == y ? p : none)
  * If there are more conjunctions in the impure source assume statement, additional functions are
  * generated to account for the semantics of the separating conjunction.
  */

object ImpureAssumeRewriter {
  val domainName = "__ns__impure_assume_rewriter"

  private def placeholderVar[S](suffix: S, typ: Type): LocalVar = LocalVar(s"__iar__dummy$suffix", typ)()
  private def placeholderVar(typ: Type): LocalVar = placeholderVar("", typ)

  private var funcs: Seq[DomainFunc] = Seq()
  private var axioms: Seq[DomainAxiom] = Seq()
  private var inverses = Seq.empty[DomainFunc]
  private var domains = Seq.empty[Domain]

  def rewrite(exp: Exp, program: Program) : Exp = {
    val collCont = scala.collection.mutable.Map.empty[Resource, Seq[((Exp, Seq[Exp]), Exp)]]

    /**
      * Rewrites assume statements:
      *   assume statements are rewritten using
      * Context: Pair of condition and variable to replace in the condition as well as the
      * permission amount
      */

    // TODO: Instead of actively doing nothing if inside a wand, the strategy simply shouldn't recurse into magic wands.
    //       I believe there is a way of defining into which nodes to recurse.

    val strat = ViperStrategy.Context[Exp]({
      case (implies: Implies, c) =>
        (implies, c.updateContext(And(c.c, implies.left)()))
      case (fap: FieldAccessPredicate, c) =>
        val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
        val dummyVar = placeholderVar(Ref)
        val newCtxFrame =  ((And(c.c, EqCmp(fap.loc.rcv, dummyVar)())(), Seq(dummyVar)), fap.perm)
        val oldCtxFrames = collCont.getOrElse(fap.loc.field, Seq())
        collCont += (fap.loc.field -> (oldCtxFrames :+ newCtxFrame))
        if (!insideWand) {
          val cp = CurrentPerm(fap.loc)(fap.pos, fap.info, fap.errT)
          val p = generatePermUsingFunc(oldCtxFrames, Seq(fap.loc.rcv), fap.perm, cp, None)
          (p, c)
        } else {
          (fap, c)
        }
      case (pred: PredicateAccessPredicate, c) =>
        val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
        val dummyVars = (LazyList.from(0) map (i => placeholderVar(i, pred.loc.loc(program).formalArgs(i).typ))) take pred.loc.args.length
        val eqs = (pred.loc.args zip dummyVars) map (a => EqCmp(a._1, a._2)())
        val cond = if (eqs.isEmpty) TrueLit()() else eqs.tail.foldLeft[Exp](eqs.head)((a, e) => And(a,e)())
        val newCtxFrame =  ((And(c.c, cond)(), dummyVars), pred.perm)
        val oldCtxFrames = collCont.getOrElse(pred.loc.loc(program), Seq())
        collCont += (pred.loc.loc(program) -> (oldCtxFrames :+ newCtxFrame))
        if (!insideWand && c.parentOption.fold(true)(!_.isInstanceOf[Unfolding])) {
          val cp = CurrentPerm(pred.loc)(pred.pos, pred.info, pred.errT)
          val p = generatePermUsingFunc(oldCtxFrames, pred.loc.args, pred.perm, cp, None)
          (p, c)
        } else {
          (pred, c)
        }
    }, TrueLit()())

    strat.execute[Exp](exp)
  }

  def rewriteInhale(inhale: Inhale) : Stmt = {
    val exps = inhale.exp match {
      case and: And => split(and)
      case other => Seq(other)
    }

//    var seq: Seq[Inhale] = Seq()
//    for (e <- exps) {
//      seq = seq :+ Inhale(e)(e.pos, e.info, e.errT)
//    }
//    val seq: Seq[Inhale] = exps.map(e => Inhale(e)(e.pos, e.info, e.errT))
//
//    val seqn = Seqn(seq, Seq())(inhale.pos, inhale.info, inhale.errT)
//    seqn

    Seqn(
      exps.map(e => Inhale(e)(e.pos, e.info, e.errT)),
      Seq()
    )(inhale.pos, inhale.info, inhale.errT)
  }

  def split(exp: Exp): Seq[Exp] = {
    exp match {
      case and: And => split(and.left) ++ split(and.right)
      case other => Seq(other)
    }
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

    val contextWithoutRcv = context

    val conds: Seq[Exp] =
      contextWithoutRcv
        .map(c => c._1._1.replace((c._1._2 zip rcv).toMap[Exp, Exp]))
        .map(e => viper.silver.ast.utility.Simplifier.simplify(e))

    if (context.isEmpty) {
      assert(conds.isEmpty)
      assert(cond.isEmpty)

      PermGeCmp(permLoc, perm)()
    } else {
      val perms: Seq[Exp] = (contextWithoutRcv map (_._2)) :+ perm

      if (funcs.length <= contextWithoutRcv.length-1) {
        val (fun, ax) = generateFunc(funcs.length + 1)
        funcs = funcs :+ fun
        axioms = axioms :+ ax
      }

      val func = funcs(contextWithoutRcv.length-1)
      val funcApp = DomainFuncApp(func, conds ++ perms, Map[TypeVar, Type]())()

      PermGeCmp(permLoc, funcApp)()
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
    val name = s"__iar__assume_helper_$numOfConds"

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
        case p: Program =>
          val assumeDomain = Domain(domainName, funcs, axioms)(info = Synthesized)

          Program(p.domains ++ domains :+ assumeDomain, p.fields, p.functions, p.predicates, p.methods, p.extensions)(p.pos, p.info, p.errT)
      }).execute(pAssume)
    }
  }
}
