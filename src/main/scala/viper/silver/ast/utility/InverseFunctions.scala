package viper.silver.ast.utility

import viper.silver.ast
import viper.silver.ast._
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion

object InverseFunctions {

  //TODO: counter parallelization problem?
  private var counter = 0

  //TODO: cache inverses?
  //TODO: identity
  //TODO: Reusing quantified variables
  def getFreshInverse(f: Forall, program: Program): (Option[(Seq[DomainFunc], Domain)], Option[Seq[Forall]], Forall) = {
    f match {
      case QuantifiedPermissionAssertion(forall, cond, acc) => {
        val domName = "Inverse_" + counter
        acc match {
          case fa: FieldAccess => {
            ???
//            val qvar = forall.variables.head
//            val r = LocalVarDecl("r", Ref)()
//            val inv = Function("inv_" + counter, Seq(r), qvar.typ, Seq(), Seq(), None, None)()
//            counter += 1
//            val invOfR = FuncApp(inv, Seq(r.localVar))()
//            val axiom1 = Forall(Seq(qvar), forall.triggers, Implies(cond, EqCmp(FuncApp(inv, Seq(fa.rcv))(), qvar.localVar)())())()
//            val axiom2 = Forall(Seq(r), Seq(Trigger(Seq(invOfR))()), Implies(cond.replace(qvar.localVar, invOfR), EqCmp(fa.rcv.replace(qvar.localVar, invOfR), r.localVar)())())()
//            val forall1 = Forall(Seq(r), Seq(Trigger(Seq(invOfR))()), forall.exp.replace(qvar.localVar, invOfR))()
//            val cond1 = cond.replace(qvar.localVar, r.localVar)
//            val acc1 = FieldAccess(r.localVar, fa.field)()
//            (Some(Seq(inv)), Some(Seq(axiom1, axiom2)), forall1)
          }
          case fap: FieldAccessPredicate => {
            val qvar = forall.variables.head
            val r = LocalVarDecl("r", Ref)()
            val inv = DomainFunc("inv_" + counter, Seq(r), qvar.typ)(domainName = domName)
            counter += 1
            val invOfR = DomainFuncApp(inv, Seq(r.localVar), Map[TypeVar, Type]())()
            val axiom1 = Forall(Seq(qvar), forall.triggers, Implies(cond, EqCmp(DomainFuncApp(inv, Seq(fap.loc.rcv), Map[TypeVar, Type]())(), qvar.localVar)())())()
            val axiom2 = Forall(Seq(r), Seq(Trigger(Seq(invOfR))()), Implies(cond.replace(qvar.localVar, invOfR), EqCmp(fap.loc.rcv.replace(qvar.localVar, invOfR), r.localVar)())())()
            val cond1 = cond.replace(qvar.localVar, invOfR)
            val acc1 = FieldAccessPredicate(FieldAccess(r.localVar, fap.loc.field)(), fap.perm.replace(qvar.localVar, invOfR))()
            val forall1 = Forall(Seq(r), Seq(Trigger(Seq(invOfR))()), Implies(cond1, acc1)())()
            val domain = Domain(domName, Seq(inv), Seq())()
            (Some((Seq(inv), domain)), Some(Seq(axiom1, axiom2)), forall1)
          }
          case pa: PredicateAccess => {
            ???
          }
          case pap: PredicateAccessPredicate => {
            val qvars = forall.variables
            val pred = pap.loc.loc(program)
            val formalArgs = pred.formalArgs
            val invs = qvars.zipWithIndex map {case (v, i) => {DomainFunc("inv_" + counter + "_" + i, formalArgs, v.typ)(domainName = domName)}}
            counter += 1
            val invsOfFormalArgs = invs map (inv => DomainFuncApp(inv, formalArgs map (_.localVar), Map[TypeVar, Type]())())
            val invArgs = invs.zipWithIndex map {case (inv, i) => {EqCmp(DomainFuncApp(inv, pap.loc.args, Map[TypeVar, Type]())(), qvars(i).localVar)()}}
            val qvarsToInv = ((qvars map (_.localVar)) zip invsOfFormalArgs).toMap
            val invArgs1 = pap.loc.args.zipWithIndex map { case (a, i) => EqCmp(a.replace(qvarsToInv), formalArgs(i).localVar)()}
            val invArgsConj = invArgs1.tail.foldLeft[Exp](invArgs1.head)((cnj, e) => And(cnj, e)())

            val axiom1 = Forall(qvars, forall.triggers, Implies(cond, invArgs.tail.foldLeft[Exp](invArgs.head)((cnj, e) => And(cnj, e)()))())()
            val axiom2 = Forall(formalArgs, Seq(Trigger(invsOfFormalArgs)()), Implies(cond.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap), invArgsConj)())()

            val cond1 = cond.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap)
            val acc1 = PredicateAccessPredicate(PredicateAccess(formalArgs map (_.localVar), pred.name)(), pap.perm.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap))()
            val forall1 = Forall(formalArgs, Seq(Trigger(invsOfFormalArgs)()), Implies(cond1, acc1)())()

            val domain = Domain(domName, invs, Seq())()
            (Some(invs, domain), Some(Seq(axiom1, axiom2)), forall1)
          }
          case wand: MagicWand => {
            val qvars = forall.variables
            val bodyVars = wand.subexpressionsToEvaluate(program)
            val formalArgs = bodyVars.indices.toList.map(i => LocalVarDecl(s"x$i", bodyVars(i).typ)())

            val invs = qvars.zipWithIndex map {case (v, i) => {DomainFunc("inv_" + counter + "_" + i, formalArgs, v.typ)(domainName = domName)}}
            counter += 1
            val invsOfFormalArgs = invs map (inv => DomainFuncApp(inv, formalArgs map (_.localVar), Map[TypeVar, Type]())())
            val invArgs = invs.zipWithIndex map {case (inv, i) => {EqCmp(DomainFuncApp(inv, bodyVars, Map[TypeVar, Type]())(), qvars(i).localVar)()}}
            val qvarsToInv = ((qvars map (_.localVar)) zip invsOfFormalArgs).toMap
            val invArgs1 = bodyVars.zipWithIndex map { case (a, i) => EqCmp(a.replace(qvarsToInv), formalArgs(i).localVar)()}
            val invArgsConj = invArgs1.tail.foldLeft[Exp](invArgs1.head)((cnj, e) => And(cnj, e)())

            val axiom1 = Forall(qvars, forall.triggers, Implies(cond, invArgs.tail.foldLeft[Exp](invArgs.head)((cnj, e) => And(cnj, e)()))())()
            val axiom2 = Forall(formalArgs, Seq(Trigger(invsOfFormalArgs)()), Implies(cond.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap), invArgsConj)())()

            val cond1 = cond.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap)
            val acc1 = wand.replace((bodyVars zip (formalArgs map (_.localVar))).toMap)
            val forall1 = Forall(formalArgs, Seq(Trigger(invsOfFormalArgs)()), Implies(cond1, acc1)())()

            val domain = Domain(domName, invs, Seq())()
            (Some(invs, domain), Some(Seq(axiom1, axiom2)), forall1)
          }
        }
      }
      case _ => (None, None, f)
    }
  }

}
