// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion

object InverseFunctions {

  private var counter = 0

  /**
    * Generates new inverse functions when used with QP assertions
    */
  def getFreshInverse(f: Forall, program: Program): (Option[(Seq[DomainFunc], Domain)], Option[Seq[Forall]], Forall) = {
    f match {
      case QuantifiedPermissionAssertion(forall, cond, acc) => {
        val domName = "Inverse_" + counter
        val info = forall.info
        val pos = forall.pos
        val errT = forall.errT
        acc match {
          case fap: FieldAccessPredicate => {
            val qvars = forall.variables
            val r = LocalVarDecl("r", Ref)()
            val invs = qvars.map(qvar => {
              val inv = DomainFunc("inv_" + counter, Seq(r), qvar.typ)(pos, info, domainName = domName, errT)
              counter += 1
              inv
            })
            val invsOfR = invs.map(inv => DomainFuncApp(inv, Seq(r.localVar), Map[TypeVar, Type]())(pos, info, errT))
            val equalities = (0 until invs.length).foldLeft(TrueLit()(): Exp)((soFar, i) => And(soFar, EqCmp(DomainFuncApp(invs(i), Seq(fap.loc.rcv), Map[TypeVar, Type]())(pos, info, errT), qvars(i).localVar)(pos, info, errT))(pos, info, errT))
            val axiom1 = Forall(qvars, forall.triggers, Implies(cond, equalities)(pos, info, errT))(pos, info, errT)
            var condReplaced = cond
            var rcvReplaced = fap.loc.rcv
            var permReplaced = fap.perm
            for (i <- 0 until qvars.length){
              condReplaced = condReplaced.replace(qvars(i).localVar, invsOfR(i))
              rcvReplaced = rcvReplaced.replace(qvars(i).localVar, invsOfR(i))
              permReplaced = permReplaced.replace(qvars(i).localVar, invsOfR(i))
            }
            val axiom2 = Forall(Seq(r), Seq(Trigger(invsOfR)(pos, info, errT)), Implies(condReplaced, EqCmp(rcvReplaced, r.localVar)(pos, info, errT))(pos, info, errT))(pos, info, errT)
            val acc1 = FieldAccessPredicate(FieldAccess(r.localVar, fap.loc.field)(), permReplaced)()
            val forall1 = Forall(Seq(r), Seq(Trigger(invsOfR)()), Implies(condReplaced, acc1)(pos, info, errT))(pos, info, errT)
            val domain = Domain(domName, invs, Seq())(pos, info, errT)
            (Some((invs, domain)), Some(Seq(axiom1, axiom2)), forall1)
          }
          case pap: PredicateAccessPredicate => {
            val qvars = forall.variables
            val pred = pap.loc.loc(program)
            val formalArgs = pred.formalArgs
            val invs = qvars.zipWithIndex map {case (v, i) => {DomainFunc("inv_" + counter + "_" + i, formalArgs, v.typ)(pos, info, domainName = domName, errT)}}
            counter += 1
            val invsOfFormalArgs = invs map (inv => DomainFuncApp(inv, formalArgs map (_.localVar), Map[TypeVar, Type]())(pos, info, errT))
            val invArgs = invs.zipWithIndex map {case (inv, i) => {EqCmp(DomainFuncApp(inv, pap.loc.args, Map[TypeVar, Type]())(pos, info, errT), qvars(i).localVar)(pos, info, errT)}}
            val qvarsToInv = ((qvars map (_.localVar)) zip invsOfFormalArgs).toMap
            val invArgs1 = pap.loc.args.zipWithIndex map { case (a, i) => EqCmp(a.replace(qvarsToInv), formalArgs(i).localVar)(pos, info, errT)}
            val invArgsConj = invArgs1.tail.foldLeft[Exp](invArgs1.head)((cnj, e) => And(cnj, e)(pos, info, errT))

            val axiom1 = Forall(qvars, forall.triggers, Implies(cond, invArgs.tail.foldLeft[Exp](invArgs.head)((cnj, e) => And(cnj, e)(pos, info, errT)))(pos, info, errT))(pos, info, errT)
            val axiom2 = Forall(formalArgs, Seq(Trigger(invsOfFormalArgs)(pos, info, errT)), Implies(cond.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap), invArgsConj)(pos, info, errT))(pos, info, errT)

            val cond1 = cond.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap)
            val acc1 = PredicateAccessPredicate(PredicateAccess(formalArgs map (_.localVar), pred.name)(pos, info, errT), pap.perm.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap))(pos, info, errT)
            val forall1 = Forall(formalArgs, Seq(Trigger(invsOfFormalArgs)(pos, info, errT)), Implies(cond1, acc1)(pos, info, errT))(pos, info, errT)

            val domain = Domain(domName, invs, Seq())(pos, info, errT)
            (Some(invs, domain), Some(Seq(axiom1, axiom2)), forall1)
          }
          case wand: MagicWand => {
            val qvars = forall.variables
            val bodyVars = wand.subexpressionsToEvaluate(program)
            val formalArgs = bodyVars.indices.toList.map(i => LocalVarDecl(s"x$i", bodyVars(i).typ)(pos, info, errT))

            val invs = qvars.zipWithIndex map {case (v, i) => {DomainFunc("inv_" + counter + "_" + i, formalArgs, v.typ)(pos, info, domainName = domName, errT)}}
            counter += 1
            val invsOfFormalArgs = invs map (inv => DomainFuncApp(inv, formalArgs map (_.localVar), Map[TypeVar, Type]())(pos, info, errT))
            val invArgs = invs.zipWithIndex map {case (inv, i) => {EqCmp(DomainFuncApp(inv, bodyVars, Map[TypeVar, Type]())(pos, info, errT), qvars(i).localVar)()}}
            val qvarsToInv = ((qvars map (_.localVar)) zip invsOfFormalArgs).toMap
            val invArgs1 = bodyVars.zipWithIndex map { case (a, i) => EqCmp(a.replace(qvarsToInv), formalArgs(i).localVar)(pos, info, errT)}
            val invArgsConj = invArgs1.tail.foldLeft[Exp](invArgs1.head)((cnj, e) => And(cnj, e)(pos, info, errT))

            val axiom1 = Forall(qvars, forall.triggers, Implies(cond, invArgs.tail.foldLeft[Exp](invArgs.head)((cnj, e) => And(cnj, e)(pos, info, errT)))(pos, info, errT))(pos, info, errT)
            val axiom2 = Forall(formalArgs, Seq(Trigger(invsOfFormalArgs)(pos, info, errT)), Implies(cond.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap), invArgsConj)(pos, info, errT))(pos, info, errT)

            val cond1 = cond.replace((qvars map (_.localVar) zip invsOfFormalArgs).toMap)
            val acc1 = wand.replace((bodyVars zip (formalArgs map (_.localVar))).toMap)
            val forall1 = Forall(formalArgs, Seq(Trigger(invsOfFormalArgs)(pos, info, errT)), Implies(cond1, acc1)(pos, info, errT))(pos, info, errT)

            val domain = Domain(domName, invs, Seq())(pos, info, errT)
            (Some(invs, domain), Some(Seq(axiom1, axiom2)), forall1)
          }
          case other => sys.error(s"found yet unsupported resource: $other")
        }
      }
      case _ => (None, None, f)
    }
  }

}
