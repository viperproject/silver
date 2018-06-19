package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter._

object AssumeRewriter {

  var funcs: Seq[Function] = Seq()
  var generated = false

  def rewrite(exp: Exp) : Exp = {

    /**
      * Context; Pair of condition and variable to replace in the condition as well as the
      * permission amount
      */

    //TODO: turn assume stmt into sequence of inhales

    val strat = ViperStrategy.Context[Seq[((Exp, Exp), Exp)]]({
      case (fap: FieldAccessPredicate, c) => {
        println(fap)
        println(c.c)
        val cp = CurrentPerm(fap.loc)(fap.pos, fap.info, fap.errT)
        //val p = generatePerm(c.c, fap.loc.rcv, fap.perm, cp)(fap.pos, fap.info, fap.errT)
        val p = generatePermUsingFunc(c.c, fap.loc.rcv, fap.perm, cp)
        println(p)
        p
      }
//      case (pred: PredicateAccessPredicate, c) => {
//        val cp = CurrentPerm(pred.loc)(pred.pos, pred.info, pred.errT)
//        val p = generatePerm(c.c, pred.loc.args, pred.perm, cp)(pred.pos, pred.info, pred.errT)
//        p
//      }
      case (forall: Forall, c) => {
        //TODO: further nesting
        val accpreds = forall.exp.subExps.filter(e => e.isInstanceOf[FieldAccessPredicate]).asInstanceOf[Seq[FieldAccessPredicate]]

        println(accpreds)
        println(accpreds.length)
        if (accpreds.isEmpty) println(forall.exp)
        if (accpreds.length > 1) sys.error("Not supported yet!")
        val fap = accpreds.head
        val cp = CurrentPerm(fap.loc)(fap.pos, fap.info, fap.errT)

        val p = generatePerm(c.c, fap.loc.rcv, fap.perm, cp)(fap.pos, fap.info, fap.errT)
        println(p)
        val f = forall.replace(accpreds.head, p)
        println(f)
        f
      }
    }, Seq(), { case (fap: FieldAccessPredicate, c) => {
      val dummyVar = LocalVar("dummy")(Ref)
      c :+ ((EqCmp(fap.loc.rcv, dummyVar)(fap.pos, fap.info, fap.errT), dummyVar), fap.perm)
    }
    case (and: And, c) => {
      val newC = c ++ update(and.left)

      newC
    }
    case (forall: Forall, c) => {
      val cond = forall.exp match {
        case impl: Implies => impl.left
        case _ => TrueLit()(forall.exp.pos, forall.exp.info, forall.exp.errT)
      }
      val accpreds = forall.exp.subExps.filter(e => e.isInstanceOf[FieldAccessPredicate]).asInstanceOf[Seq[FieldAccessPredicate]]
      val varsToReplace = accpreds.map(fp => fp.loc.rcv)
      val perms = accpreds.map(fp => fp.perm)

      c :+ ((cond, varsToReplace.head), perms.head)
    }
    })

    strat.execute(exp)
  }

  def update(node: Node): Seq[((Exp, Exp), Exp)] = {
    node match {
      case fp: FieldAccessPredicate => {
        val dummyVar = LocalVar("dummy")(Ref)
        Seq(((EqCmp(fp.loc.rcv, dummyVar)(fp.pos, fp.info, fp.errT), dummyVar), fp.perm))
      }
      case forall: Forall => {
        val cond = forall.exp match {
          case impl: Implies => impl.left
          case _ => TrueLit()(forall.exp.pos, forall.exp.info, forall.exp.errT)
        }
        val accpreds = forall.exp.subExps.filter(e => e.isInstanceOf[FieldAccessPredicate]).asInstanceOf[Seq[FieldAccessPredicate]]
        val varsToReplace = accpreds.map(fp => fp.loc.rcv)
        val perms = accpreds.map(fp => fp.perm)

        Seq(((cond, varsToReplace.head), perms.head))
      }
      case n => n.subnodes flatMap update
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

  def generateCondition(condsWithPerm: Seq[((Exp, Exp), Exp)], rcv: Exp, perm: Exp)
                       (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos) : (Exp, Exp) = {
    val conds = condsWithPerm map (_._1)
    val perms = condsWithPerm map (_._2)

    var newConds : Seq[Exp] = Seq()
    for (c <- conds) {
      newConds = newConds :+ c._1.replace(c._2, rcv)
    }

    val cnj = newConds.tail.foldLeft[Exp](newConds.head)((a, e) => And(a, e)(pos, info, errT))
    val sum = perms.foldLeft[Exp](perm)((s, p) => PermAdd(s, p)(pos, info, errT))

    (cnj, sum)
  }

  def generatePerm(context: Seq[((Exp, Exp), Exp)], rcv: Exp, perm: Exp, permLoc: CurrentPerm)
                  (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): Exp = {

    val contextWithoutRcv = context.filter(c => !c._1._1.contains(rcv))
    if (contextWithoutRcv.isEmpty) return PermGeCmp(permLoc, perm)(pos, info, errT)

    var condSeq : Seq[(Exp, Exp)] = Seq()

    for (i <- contextWithoutRcv.length until 0 by -1) {
      val combinations = contextWithoutRcv.combinations(i)
      for (c <- combinations) {
        condSeq = condSeq :+ generateCondition(c, rcv, perm)(pos, info, errT)
      }
    }

    val cond = generateExp(condSeq, perm)(pos, info, errT)

    val p = PermGeCmp(permLoc, cond)(pos, info, errT)
    println(p)
    p
  }

  def generatePermUsingFunc(context: Seq[((Exp, Exp), Exp)], rcv: Exp, perm: Exp, permLoc: CurrentPerm): Exp = {

    val contextWithoutRcv = context.filter(c => !c._1._1.contains(rcv))
    if (contextWithoutRcv.isEmpty) return PermGeCmp(permLoc, perm)()

    val conds = contextWithoutRcv map (c => c._1._1.replace(c._1._2, rcv))
    val perms = (contextWithoutRcv map (_._2)) :+ perm

    val func = funcs(contextWithoutRcv.length-1)
    val funcApp = FuncApp(func, conds ++ perms)()
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

  def generateFunc(numOfConds: Int): Function = {
    val name = "assume_helper_" + numOfConds
    var conds: Seq[LocalVar] = Seq()
    var perms: Seq[LocalVar] = Seq()
    var cDecls: Seq[LocalVarDecl] = Seq()
    var pDecls: Seq[LocalVarDecl] = Seq(LocalVarDecl("p_0", Perm)())
    val formalArgs = {
      for (i <- 0 until numOfConds) {
        cDecls = LocalVarDecl("c_" + (i+1), Bool)() +: cDecls
        if (i < numOfConds-1) conds = conds :+ LocalVar("c_" + (i+1))(Bool)
      }
      for (i <- 0 until numOfConds) {
        pDecls = LocalVarDecl("p_" + (i+1), Perm)() +: pDecls
        if (i < numOfConds-1) perms = perms :+ LocalVar("p_" + (i+1))(Perm)
      }
      cDecls ++ pDecls
    }
    val body = {
      val condsWithPerm = conds zip perms

      var condSeq: Seq[(Exp, Exp)] = Seq()
      for (i <- numOfConds until 0 by -1) {
        for (c <- condsWithPerm.combinations(i)) {
          val funC = genFuncCond(c, LocalVar("p_0")(Perm))
          val cnj = And(LocalVar("c_" + numOfConds)(Bool), funC._1)()
          val sum = PermAdd(LocalVar("p_" + numOfConds)(Perm), funC._2)()
          condSeq = condSeq :+ (cnj, sum)
        }
      }

      condSeq = condSeq :+ (LocalVar("c_" + numOfConds)(Bool), PermAdd(LocalVar("p_" + numOfConds)(Perm), LocalVar("p_0")(Perm))())

      if (numOfConds > 1) {
        val funcName = "assume_helper_" + (numOfConds-1)
        Some(generateExp(condSeq, FuncApp(funcName, conds ++ perms :+ LocalVar("p_0")(Perm))(NoPosition, NoInfo, Perm, cDecls.tail ++ pDecls.tail, NoTrafos))())
      } else {
        val c1 = LocalVar("c_1")(Bool)
        val p1 = LocalVar("p_1")(Perm)
        val p0 = LocalVar("p_0")(Perm)
        Some(CondExp(c1, PermAdd(p1, p0)(), p0)())
      }
    }
    Function(name, formalArgs, Perm, Seq(), Seq(), None, body)()
  }

  def genFuncCond(condsWithPerm: Seq[(Exp, Exp)], perm: Exp): (Exp, Exp) = {
    val conds = condsWithPerm map (_._1)
    val perms = condsWithPerm map (_._2)

    val cnj = conds.tail.foldLeft[Exp](conds.head)((e, v) => And(e, v)())
    val sum = perms.foldLeft[Exp](perm)((e, v) => PermAdd(e, v)())

    (cnj, sum)
  }

  def addFuncs(p: Program): Program = {

    if (!generated) {
      for (i <- 1 until 9) {
        funcs = funcs :+ generateFunc(i)
      }
      generated = true
    }

    ViperStrategy.Slim({
      case p: Program => Program(p.domains, p.fields, p.functions ++ funcs, p.predicates, p.methods)(p.pos, p.info, p.errT)
      case a: Assume => rewriteInhale(Inhale(rewrite(a.exp))(a.pos))
    }).execute(p)
  }

  //TODO: second set of args
  //TODO: comparison to self
  /**
    * x = y ? px + py : px
    * for resources r1, r2: compare args
    */
}
