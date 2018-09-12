package viper.silver.ast.utility

import viper.silver.ast
import viper.silver.ast._
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.ast.utility.Rewriter._

object AssumeRewriter {

  var funcs: Seq[DomainFunc] = Seq()
  var axioms: Seq[DomainAxiom] = Seq()
  var inverses = Seq.empty[DomainFunc]
  var domains = Seq.empty[Domain]

  def rewrite(exp: Exp, program: Program) : Exp = {

    /**
      * Context: Pair of condition and variable to replace in the condition as well as the
      * permission amount
      */

    val strat = ViperStrategy.Context[Map[Resource, Seq[((Exp, Seq[Exp]), Exp)]]]({
      case (fap: FieldAccessPredicate, c) => {
        val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
        if (!insideWand) {
          val cp = CurrentPerm(fap.loc)(fap.pos, fap.info, fap.errT)
          //val p = generatePerm(c.c, fap.loc.rcv, fap.perm, cp)(fap.pos, fap.info, fap.errT)
          val p = generatePermUsingFunc(c.c.getOrElse(fap.loc.field, Seq()), Seq(fap.loc.rcv), fap.perm, cp, None)
          p
        } else {
          fap
        }
      }
      case (pred: PredicateAccessPredicate, c) => {
        val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
        if (!insideWand && !c.parent.isInstanceOf[Unfolding]) {
          val cp = CurrentPerm(pred.loc)(pred.pos, pred.info, pred.errT)
          val p = generatePermUsingFunc(c.c.getOrElse(pred.loc.loc(program), Seq()), pred.loc.args, pred.perm, cp, None)
          p
        } else {
          pred
        }
      }
      case (wand: MagicWand, c) => {
        if (!c.parent.isInstanceOf[CurrentPerm] && !c.parent.isInstanceOf[Trigger] && !c.parent.isInstanceOf[Applying]) {
          val cp = CurrentPerm(wand)(wand.pos, wand.info, wand.errT)
          val p = generatePermUsingFunc(c.c.getOrElse(wand.structure(program), Seq()), wand.subexpressionsToEvaluate(program), FullPerm()(), cp, None)
          p
        } else {
          wand
        }
      }
      case (QuantifiedPermissionAssertion(forall, cond, acc), c) => {
        acc match {
          case fap: FieldAccessPredicate => {
            val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
            if (!insideWand) {
              val cp = CurrentPerm(fap.loc)(fap.pos, fap.info, fap.errT)
              val p = generatePermUsingFunc(c.c.getOrElse(fap.loc.field, Seq()), Seq(fap.loc.rcv), fap.perm, cp, Some(cond))
              forall.replace(acc, p)
            } else {
              forall
            }
          }
          case pred: PredicateAccessPredicate => {
            val insideWand = c.ancestorList.foldLeft[Boolean](false)((b, n) => b || n.isInstanceOf[MagicWand])
            if (!insideWand) {
              val cp = CurrentPerm(pred.loc)(pred.pos, pred.info, pred.errT)
              val p = generatePermUsingFunc(c.c.getOrElse(pred.loc.loc(program), Seq()), pred.loc.args, pred.perm, cp, Some(cond))
              forall.replace(acc, p)
            } else {
              forall
            }
          }
          case wand: MagicWand => {
            if (!c.parent.isInstanceOf[CurrentPerm]) {
              val cp = CurrentPerm(wand)(wand.pos, wand.info, wand.errT)
              val p = generatePermUsingFunc(c.c.getOrElse(wand.structure(program), Seq()), wand.subexpressionsToEvaluate(program), FullPerm()(), cp, Some(cond))
              forall.replace(acc, p)
            } else {
              forall
            }
          }
        }
      }
    }, Map(): Map[Resource, Seq[((Exp, Seq[Exp]), Exp)]], {
      case (fap: FieldAccessPredicate, c) => {
        val dummyVar = LocalVar("dummy")(Ref)
        c + (fap.loc.field -> (c.getOrElse(fap.loc.field, Seq()) :+ ((EqCmp(fap.loc.rcv, dummyVar)(fap.pos, fap.info, fap.errT), Seq(dummyVar)), fap.perm)))
      }
      case (pred: PredicateAccessPredicate, c) => {
        val dummyVars = (Stream.from(0) map (i => LocalVar("dummy" + i)(pred.loc.loc(program).formalArgs(i).typ))) take pred.loc.args.length
        val eqs = (pred.loc.args zip dummyVars) map (a => EqCmp(a._1, a._2)())
        val cond = eqs.tail.foldLeft[Exp](eqs.head)((a, e) => And(a,e)())
        c + (pred.loc.loc(program) -> (c.getOrElse(pred.loc.loc(program), Seq()) :+ ((cond, dummyVars), pred.perm)))
      }
      case (wand: MagicWand, c) => {
        val dummyVars = (Stream.from(0) map (i => LocalVar("dummy" + i)(wand.structure(program).subexpressionsToEvaluate(program)(i).typ))) take wand.subexpressionsToEvaluate(program).length
        val eqs = (wand.subexpressionsToEvaluate(program) zip dummyVars) map (a => EqCmp(a._1, a._2)())
        val cond = eqs.tail.foldLeft[Exp](eqs.head)((a, e) => And(a,e)())
        c + (wand.structure(program) -> (c.getOrElse(wand.structure(program), Seq()) :+ ((cond, dummyVars), FullPerm()())))
      }
      case (and: And, c) => {
        val lupdate = update(and.left, program)
        val newC = lupdate map (lu => {
          val update = c.getOrElse(lu._1, Seq())
          (lu._1, lu._2 ++ update)
        })
        c ++ newC
      }
      case (QuantifiedPermissionAssertion(forall, cond, acc), c) => {

        acc match {
          case fap: FieldAccessPredicate => {
            c + (fap.loc.field -> (c.getOrElse(fap.loc.field, Seq()) :+ ((cond, forall.variables map (_.localVar)), fap.perm)))
          }
          case pred: PredicateAccessPredicate => {
            c + (pred.loc.loc(program) -> (c.getOrElse(pred.loc.loc(program), Seq()) :+ ((cond, forall.variables map (_.localVar)), pred.perm)))
          }
          case wand: MagicWand => {
            c + (wand.structure(program) -> (c.getOrElse(wand.structure(program), Seq()) :+ ((cond, forall.variables map (_.localVar)), FullPerm()())))
          }
        }
      }
    })

    strat.execute(exp)
  }

  def update(node: Node, program: Program): Seq[(Resource, Seq[((Exp, Seq[Exp]), Exp)])] = {
    node match {
      case fp: FieldAccessPredicate => {
        val dummyVar = LocalVar("dummy")(Ref)
        Seq(fp.loc.field -> Seq(((EqCmp(fp.loc.rcv, dummyVar)(fp.pos, fp.info, fp.errT), Seq(dummyVar)), fp.perm)))
      }
      case pred: PredicateAccessPredicate => {
        val dummyVars = (Stream.from(0) map (i => LocalVar("dummy" + i)(pred.loc.loc(program).formalArgs(i).typ))) take pred.loc.args.length
        val eqs = (pred.loc.args zip dummyVars) map (a => EqCmp(a._1, a._2)())
        val cond = eqs.tail.foldLeft[Exp](eqs.head)((a, e) => And(a,e)())
        Seq(pred.loc.loc(program) -> Seq(((cond, dummyVars), pred.perm)))
      }
      case wand: MagicWand => {
        val dummyVars = (Stream.from(0) map (i => LocalVar("dummy" + i)(wand.structure(program).subexpressionsToEvaluate(program)(i).typ))) take wand.subexpressionsToEvaluate(program).length
        val eqs = (wand.subexpressionsToEvaluate(program) zip dummyVars) map (a => EqCmp(a._1, a._2)())
        val cond = eqs.tail.foldLeft[Exp](eqs.head)((a, e) => And(a,e)())
        Seq(wand.structure(program) -> Seq(((cond, dummyVars), FullPerm()())))
      }
      case QuantifiedPermissionAssertion(forall, cond, acc) => {

        acc match {
          case fap: FieldAccessPredicate => {
            Seq(fap.loc.field -> Seq(((cond, forall.variables map (_.localVar)), fap.perm)))
          }
          case pred: PredicateAccessPredicate => {
            Seq(pred.loc.loc(program) -> Seq(((cond, forall.variables map (_.localVar)), pred.perm)))
          }
          case wand: MagicWand => {
            Seq(wand.structure(program) -> Seq(((cond, forall.variables map (_.localVar)), FullPerm()())))
          }
        }
      }
      case n => {
        val subUpdate = n.subnodes flatMap (sub => update(sub, program))
        subUpdate.groupBy(_._1).map { case (k,v) => (k, v.flatMap(_._2))} toSeq
      }
    }
  }

  def rewriteInhale(inhale: Inhale) : Stmt = {

    var seq: Seq[Inhale] = Seq()
    val exps = inhale.exp match {
      case and: And => split(and)
      case other => Seq(other)
    }

    for (e <- exps) {
      seq = seq :+ Inhale(e)()
    }

    val seqn = Seqn(seq, Seq())(inhale.pos, inhale.info, inhale.errT)
    seqn
  }

  def generatePermUsingFunc(context: Seq[((Exp, Seq[Exp]), Exp)], rcv: Seq[Exp], perm: Exp, permLoc: CurrentPerm, cond: Option[Exp]): Exp = {

    assert(context.forall(c => c._1._2.length == rcv.length))

    val contextWithoutRcv = cond match {
      case Some(exp) => {
        context.filter(c => !c._1._1.equals(exp))
      }
      case None => {
        context.filter(c => !rcv.forall(e => c._1._1.contains(e)))
      }
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

  def generateExp(conds: Seq[(Exp, Exp)], perm: Exp)
                 (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Exp = {
    if (conds.isEmpty) return perm
    val head = conds.head
    val cond = head._1
    val thn = head._2
    val otherwise = generateExp(conds.tail, perm)(pos, info, errT)
    CondExp(cond, thn, otherwise)(pos, info, errT)
  }

  def split(exp: Exp): Seq[Exp] = {
    exp match {
      case and: And => split(and.left) ++ split(and.right)
      case other => Seq(other)
    }
  }

  def generateFunc(numOfConds: Int): (DomainFunc, DomainAxiom) = {
    val name = "assume_helper_" + numOfConds
    var conds: Seq[LocalVar] = Seq()
    var perms: Seq[LocalVar] = Seq()
    var cDecls: Seq[LocalVarDecl] = Seq()
    var pDecls: Seq[LocalVarDecl] = Seq(LocalVarDecl("p_0", Perm)())
    val formalArgs = {
      for (i <- 0 until numOfConds) {
        cDecls = LocalVarDecl("c_" + (i+1), Bool)() +: cDecls
        if (i < numOfConds) conds = conds :+ LocalVar("c_" + (i+1))(Bool)
      }
      for (i <- 0 until numOfConds) {
        pDecls = LocalVarDecl("p_" + (i+1), Perm)() +: pDecls
        if (i < numOfConds) perms = perms :+ LocalVar("p_" + (i+1))(Perm)
      }
      cDecls ++ pDecls
    }
    val body = {
      val condsWithPerm = conds zip perms

      val condExps = condsWithPerm map (cp => CondExp(cp._1, cp._2, NoPerm()())())
      condExps.foldLeft[Exp](LocalVar("p_0")(Perm))((p, c) => PermAdd(p, c)())
    }
    val fun = DomainFunc(name, formalArgs, Perm)(domainName = "Assume")
    val ax = Forall(formalArgs, Seq(Trigger(Seq(DomainFuncApp(fun, (formalArgs map (_.localVar)), Map[TypeVar, Type]())()))()), EqCmp(DomainFuncApp(fun, (formalArgs map (_.localVar)), Map[TypeVar, Type]())(), body)())()
    val dax = DomainAxiom(name + "_axiom", ax)(domainName = "Assume")
    (fun, dax)
  }

  def genFuncCond(condsWithPerm: Seq[(Exp, Exp)], perm: Exp): (Exp, Exp) = {
    val conds = condsWithPerm map (_._1)
    val perms = condsWithPerm map (_._2)

    val cnj = conds.tail.foldLeft[Exp](conds.head)((e, v) => And(e, v)())
    val sum = perms.foldLeft[Exp](perm)((e, v) => PermAdd(e, v)())

    (cnj, sum)
  }

  def rewriteQPs(exp: Exp, program: Program): Exp = {
    exp match {
      case forall: Forall => {
        val invForall = InverseFunctions.getFreshInverse(forall, program)
        invForall match {
          case (Some((invs, domain)), Some(axs), forall1) => {
            inverses ++= invs
            domains :+= domain
            val ax = axs.tail.foldLeft[Exp](axs.head)((e, f) => And(e, f)())
            And(ax, forall1)()
          }
          case _ => forall
        }
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

    ViperStrategy.Slim({
      case p: Program => Program(p.domains ++ domains :+ Domain("Assume", funcs, axioms)(), p.fields, p.functions, p.predicates, p.methods)(p.pos, p.info, p.errT)
    }).execute(pAssume)
  }
}
