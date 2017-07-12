/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import org.scalatest.tools.ReporterConfigurations
import viper.silver.ast._
import viper.silver.verifier.errors.{AssertFailed, TerminationFailed}
import viper.silver.verifier.reasons._

import scala.collection.mutable

/** Utility methods for DecreaseClauses. */
object DecreasesClause {

  //TODO
  // multiple function calls -> multiple assertions
  def addMethods(funcs: Seq[Function], decreasingFunc: DomainFunc, boundedFunc: DomainFunc, nestedFunc: DomainFunc, locDomain: Domain, findFnc: (String) => Function, predicates: Seq[Predicate]): Seq[Method] = {
    val methods = funcs map (addTerminationProof(_, decreasingFunc, boundedFunc, nestedFunc, locDomain, findFnc, predicates))
    methods
  }

  var createdDomains: Seq[Domain] = Nil
  var neededLocalVars: Seq[LocalVarDecl] = Nil

  def addDomains(predicates: Seq[Predicate], locDomain: Domain): Seq[Domain] = {

    //TODO store these Domains local

    //Add necessary functions in the domain Loc[T]
    assert(locDomain.typVars.size == 1)
    //assert (locDomain.functions.isEmpty) //for testing commented
    //Add a function for each signature of predicate into the Location Domain
    predicates.foreach { p =>
      val funcName: String = "loc_" + p.formalArgs.map(_.typ).mkString("_")
      //if signature not already added
      if (locDomain.functions.filter(_.name == funcName).isEmpty) {
        locDomain.functions :+= DomainFunc(funcName, p.formalArgs, DomainType(locDomain, Map(locDomain.typVars.head -> locDomain.typVars.head)), false)(locDomain.pos, locDomain.info, locDomain.name, locDomain.errT)
      }
    }

    ////////////////////////////////////////////////
    //Add necessay Domains
    createdDomains = predicates map { pred =>
      Domain(pred.name + "_PredName", Seq(), Seq(), Seq())(NoPosition) //pege TODO Position?
    }
    createdDomains
  }

  private def addTerminationProof(func: Function, decreasingFunc: DomainFunc, boundedFunc: DomainFunc, nestedFunc: DomainFunc, locDomain: Domain, findFnc: (String) => Function, predicates: Seq[Predicate]): Method = {
    println("DecClauses: ")

    func.decs match {
      case Some(DecStar()) => println("*")
      case Some(DecTuple(e)) => println(e)
      case d =>
    }

    val m = Method(func.name + "_termination_proof", func.formalArgs, Seq(), func.pres, Nil, Nil, Statements.EmptyStmt)(NoPosition, func.info, func.errT)
    m.body = rewriteFuncBodyAsStmts(func.body.get, decreasingFunc, boundedFunc, nestedFunc, locDomain, func, Set(), findFnc, predicates)
    m.locals = neededLocalVars
    m
  }



  def rewriteFuncBodyAsStmts(body: Exp, decreasingFunc: DomainFunc, boundedFunc: DomainFunc, nestedFunc: DomainFunc, locDmain: Domain, func: Function, alreadyChecked: Set[String], findFnc: (String) => Function, predicates: Seq[Predicate]): Stmt = {

    //Replace all the variables with the called Arguments (Used especially i mutual recursion)
    //TODO replace is only right after a function call -> do it there directly
    //val body = b.replace(callerArgs)

    //TODO replace
    body match {
      case p: AccessPredicate => p match {
        case FieldAccessPredicate(loc, perm) => Statements.EmptyStmt //important?
        case pap: PredicateAccessPredicate =>
          val pred: Predicate = predicates.filter(_.name == pap.loc.predicateName).head //predicates use of?

          pred.body match {
            case Some(body) =>
              val res = rewritePredBodyAsExp(body, pap, nestedFunc, locDmain)
              neededLocalVars = res._2
              res._1
            case None => Statements.EmptyStmt
          }

      }
      case InhaleExhaleExp(in, ex) => Statements.EmptyStmt
      case _: PermExp => Statements.EmptyStmt
      case _: LocationAccess => Statements.EmptyStmt
      case CondExp(cond, thn, els) =>
        val s1 = rewriteFuncBodyAsStmts(cond, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates)
        val s2 = If(cond, rewriteFuncBodyAsStmts(thn, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates), rewriteFuncBodyAsStmts(els, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates))(body.pos)
        Seqn(Seq(s1, s2))(body.pos)
      case Unfolding(acc, unfBody) =>
        val s1 = Unfold(acc)(unfBody.pos)
        val s2 = rewriteFuncBodyAsStmts(acc, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates)
        val s3 = rewriteFuncBodyAsStmts(unfBody, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates)
        val s4 = Fold(acc)(unfBody.pos)
        Seqn(Seq(s1, s2, s3, s4))(unfBody.pos)
      case _: GhostOperation => Statements.EmptyStmt
      case Let(variable, exp, body) => Statements.EmptyStmt
      case _: QuantifiedExp => Statements.EmptyStmt
      case ForPerm(variable, accessList, body) => Statements.EmptyStmt
      case _: AbstractLocalVar => Statements.EmptyStmt
      case _: SeqExp => Statements.EmptyStmt
      case _: SetExp => Statements.EmptyStmt
      case _: MultisetExp => Statements.EmptyStmt
      case _: Literal => Statements.EmptyStmt

      //case tr: PossibleTrigger =>

      //------------------------------
      //Other Triggers?
      case callee: FuncApp =>

        //TODO

        //check if calledFunc is itself
        //yes do checks
        //no look for itself name: look rec and store already discovered
        //adjust args and give further
        //if found give arg back with conditions

        //method searchFunctionCall(FuncName : String, args) : //maybe not all args
        // (new arg, conditions) //errors?

        var dec = func.decs

        //If no decreasing argument is given, try to proof termination by decreasing the first argument
        //        if (decClause.isEmpty) {
        //          decClause = Seq(LocalVar(func.formalArgs.head.name)(func.formalArgs.head.typ))
        //        }

        val calleeArgs = callee.getArgs
        val termCheckOfArgs = calleeArgs map (rewriteFuncBodyAsStmts(_, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates))


        //Assume only one decreasesClause
        //TODO multiples decreasesClauses


        val paramTypesDecr = decreasingFunc.formalArgs map (_.typ)
        val argTypeVarsDecr = paramTypesDecr.flatMap(p => p.typeVariables)

        //val argTypes = (callee.getArgs map (_.typ))
        //val map = (argTypeVars zip argTypes).toMap

        //var mapDecr = Map(argTypeVarsDecr.head -> decClause.head.typ)

        ///////

        //Called Function is not the original function (no recursion so far)
        if (callee.funcname != func.name) {
          if (!alreadyChecked.contains(callee.funcname)) {
            val newFunc = findFnc(callee.funcname)
            //val m3 = searchMutualRecursion(newFunc, newFunc.body.get, calleeArgs, func.name, TrueLit()(NoPosition), members)
            //val newArgs = callee.getArgs map (_.replace((callee.formalArgs zip callerArgs.values).toMap))

            newFunc.decs match {

              case Some(DecStar()) =>
                //The called Function does not terminate
                println("Error - The called Function does not terminate (*)")

                val errTr = ErrTrafo({ case AssertFailed(_, r) => TerminationFailed(callee, r match {
                  case _: AssertionFalse => CallingNonTerminatingFunction(body, func.name, callee.funcname)
                  case k => k
                })
                })

                Seqn(termCheckOfArgs ++ Seq(Assert(FalseLit()(func.pos))(pos = func.pos, info = SimpleInfo(Seq("Called Fnc (" + callee.funcname + ") does not terminate")), errT = errTr)))(body.pos)

              case _ =>
                //search for a recursion in the called function
                val newFormalArgs = callee.formalArgs map {
                  case l: LocalVarDecl => LocalVar(l.name)(l.typ) //, l.pos, l.info, l.errT)
                  case a => a
                }

                var body = newFunc.body.get
                //body = body.replace((newFormalArgs.asInstanceOf[Seq[Exp]] zip calleeArgs).toMap)
                body = body.replace((newFormalArgs zip calleeArgs).toMap)
                val termCheckOfFuncBody = rewriteFuncBodyAsStmts(body, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked ++ Set(callee.funcname), findFnc, predicates)
                Seqn(termCheckOfArgs ++ Seq(termCheckOfFuncBody))(body.pos)
            }
          } else {
            Seqn(termCheckOfArgs)(body.pos)
          }

        } else {
          //Called Function is the same as the original one => recursion detected

          if (dec.isEmpty) { //TODO isDefined or isEmpty?
            //There is a decrease Clause //TODO no decClause size=0
            //Give an error, because you have recursion but no decreases clause
            println("Error - There is recursion but no decClause defined - " + func.name)

            val errTr = ErrTrafo({ case AssertFailed(_, r) => TerminationFailed(callee, r match {
              case _: AssertionFalse => NoDecClauseSpecified(body, callee.funcname)
              case k => k
            })
            })

            Assert(FalseLit()(func.pos))(pos = func.pos, info = SimpleInfo(Seq("Recursion but no decClause")), errT = errTr)
          }
          else {
            //Replace in the decreaseClause every argument with the correct call
            //TODO are there other AccessPredicate?
            //Change Predicates to Functions
            //Becuase Predicate might not be pure and thus is not allowed as arguments in DomainFunctions
            //            val decClauseWithoutPred = decClause map (_ match {
            //              case pred: PredicateAccessPredicate =>
            //                val args = pred.loc.args
            //                val formArgs = args map (a => LocalVarDecl(a.toString(), a.typ)(NoPosition))
            //
            //                //FuncApp("InsidePredicate", Seq(pred.loc))(NoPosition, NoInfo, Bool, Seq(LocalVarDecl(pred.loc.predicateName, pred.loc.typ)(NoPosition)), NoTrafos)
            //                FuncApp(pred.loc.predicateName, pred.loc.args)(NoPosition, NoInfo, Bool, formArgs, NoTrafos)
            //
            //              //LocalVarDecl(name: String, typ: Type)
            //              case d => d
            //            })
            dec match {
              case Some(DecTuple(decClause)) =>

                //Cast Arguments to LocalVariables
                val formalArgs = func.formalArgs map {
                  case l: LocalVarDecl => LocalVar(l.name)(l.typ) //, l.pos, l.info, l.errT)
                  case a => a
                }

                val smallerExpression = decClause map (_.replace((formalArgs zip calleeArgs).toMap))
                val biggerExpression = decClause map addOldIfNecessary

                val pos = body.pos
                val infoBound = SimpleInfo(Seq("BoundedCheck"))
                val infoDecr = SimpleInfo(Seq("DecreasingCheck"))

                val errTBound = ErrTrafo({ case AssertFailed(_, r) => TerminationFailed(callee, r match {
                  case k: AssertionFalse => TerminationNoBound(decClause.head, decClause) //TODO head is not correct
                  case k => k
                })
                })

                val errTDecr = ErrTrafo({ case AssertFailed(_, r) => TerminationFailed(callee, r match {
                  case _: AssertionFalse => TerminationMeasure(decClause.head, decClause) //TODO head is not correct
                  case k => k
                })
                })

                val e = smallerExpression zip biggerExpression

                var decrFunc = Seq.empty[Exp]
                var boundFunc = Seq.empty[Exp]

                for (i <- e.indices) {
                  if (i > 0) {
                    decrFunc :+= EqCmp(e(i - 1)._1, e(i - 1)._2)(decreasingFunc.pos)
                  }
                  decrFunc :+= DomainFuncApp(decreasingFunc, Seq(e(i)._1, e(i)._2), Map(argTypeVarsDecr.head -> e(i)._2.typ))(decreasingFunc.pos)
                  boundFunc :+= DomainFuncApp(boundedFunc, Seq(e(i)._1), Map(argTypeVarsDecr.head -> e(i)._1.typ))(boundedFunc.pos)
                }

                val boundedAss = Assert(buildBoundTree(boundFunc))(pos, infoBound, errTBound)
                val decreaseAss = Assert(buildDecTree(decrFunc, conj = true))(pos, infoDecr, errTDecr) //TODO mapDecr

                Seqn(termCheckOfArgs ++ Seq(boundedAss, decreaseAss))(pos) //TODO Position?

              case Some(DecStar()) =>
                //Do Nothing -> Users says that function will not terminate
                Statements.EmptyStmt
              case None => Statements.EmptyStmt
            }
          }
        }

      case b: BinExp => Seqn(Seq(rewriteFuncBodyAsStmts(b.left, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates), rewriteFuncBodyAsStmts(b.right, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates)))(body.pos)
      case u: UnExp => rewriteFuncBodyAsStmts(u.exp, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates)
      case _: Lhs => Statements.EmptyStmt
      case k: ForbiddenInTrigger => k match {
        case CondExp(cond, thn, els) => Statements.EmptyStmt
        case _: DomainOpExp => Statements.EmptyStmt
      }
      case f: FuncLikeApp => f match {
        case FuncApp(funcname, args) => Statements.EmptyStmt
        case _: AbstractDomainFuncApp => Statements.EmptyStmt
      }
      case _ =>
        Statements.EmptyStmt
    }
  }

  def rewritePredBodyAsExp(body: Exp, origPred: PredicateAccessPredicate, nestedFunc: DomainFunc, locDomain: Domain): (Stmt, Seq[LocalVarDecl]) = {
    body match {
      case predi: AccessPredicate => predi match {
        case FieldAccessPredicate(loc, perm) => (Statements.EmptyStmt, Seq())
        case calledPred: PredicateAccessPredicate =>

          val domainOfCallerPred: Domain = createdDomains.filter(_.name == (origPred.loc.predicateName + "_PredName")).head
          val domainOfCalleePred: Domain = createdDomains.filter(_.name == (calledPred.loc.predicateName + "_PredName")).head

          val callerPredName = origPred.loc.predicateName + "_" + origPred.loc.args.map(_.toString()).mkString("_").replace(".","")
          val calleePredName = calledPred.loc.predicateName + "_" + calledPred.loc.args.map(_.toString()).mkString("_").replace(".","")
          val varOfCallerPred = LocalVar(callerPredName)(DomainType(locDomain, Map(TypeVar(locDomain.typVars.head.name) -> DomainType(domainOfCallerPred, Map()))), calledPred.pos)
          val varOfCalleePred = LocalVar(calleePredName)(DomainType(locDomain, Map(TypeVar(locDomain.typVars.head.name) -> DomainType(domainOfCalleePred, Map()))), calledPred.pos)

          val varDeclCallerPred: LocalVarDecl = LocalVarDecl(varOfCallerPred.name, varOfCallerPred.typ)(varOfCallerPred.pos)
          val varDeclCalleePred: LocalVarDecl = LocalVarDecl(varOfCalleePred.name, varOfCalleePred.typ)(varOfCalleePred.pos)

          //TODO method generateSignature()
          val funcNameCaller: String = "loc_" + origPred.loc.args.map(_.typ).mkString("_")
          val funcNameCallee: String = "loc_" + calledPred.loc.args.map(_.typ).mkString("_")

          val domainFuncOut: DomainFunc = locDomain.functions.filter(_.name == funcNameCaller).head
          val mapOut: Map[TypeVar, Type] = Map(TypeVar(locDomain.typVars.head.name) -> DomainType(domainOfCallerPred, Map()))
          val outSideFunc = DomainFuncApp(domainFuncOut, origPred.loc.args, mapOut)(calledPred.pos)
          val assign1 = LocalVarAssign(varOfCallerPred, outSideFunc)(calledPred.pos)

          val domainFuncIn = locDomain.functions.filter(_.name == funcNameCallee).head
          val mapIn: Map[TypeVar, Type] = Map(TypeVar(locDomain.typVars.head.name) -> DomainType(domainOfCalleePred, Map()))
          val inSideFunc = DomainFuncApp(domainFuncIn, calledPred.loc.args, mapIn)(calledPred.pos)
          val assign2 = LocalVarAssign(varOfCalleePred, inSideFunc)(calledPred.pos)

          val mapNested: Map[TypeVar, Type] = Map(TypeVar("N1") -> DomainType(domainOfCalleePred, Map()), TypeVar("N2") -> DomainType(domainOfCallerPred, Map()))
          val assume = Inhale(DomainFuncApp(nestedFunc, Seq(varOfCalleePred, varOfCallerPred), mapNested)(calledPred.pos))(calledPred.pos)
          //Inhale()

          //only use LocalVarAssign => Seq(Assign1, assign2))
          (Seqn(Seq(assign1, assign2, assume))(calledPred.pos), Seq(varDeclCallerPred, varDeclCalleePred))


        //nested(var2, var1)
        //
        //              FuncApp(nestedFunc.name, Seq())(pred.pos, nestedFunc.typ, nestedFunc.formalArgs)
      }
      case c: CondExp =>
        val thn = rewritePredBodyAsExp(c.thn, origPred, nestedFunc, locDomain)
        val els = rewritePredBodyAsExp(c.els, origPred, nestedFunc, locDomain)
        (If(c.cond,thn._1, els._1)(c.pos),thn._2 ++ els._2)
      case b: BinExp =>
        val left = rewritePredBodyAsExp(b.left, origPred, nestedFunc, locDomain)
        val right = rewritePredBodyAsExp(b.right, origPred, nestedFunc, locDomain)
        (Seqn(Seq(left._1,right._1))(b.pos),left._2 ++ right._2)
      case u: UnExp => rewritePredBodyAsExp(u.exp, origPred, nestedFunc, locDomain)
      //case Implies =>
      case _ => (Statements.EmptyStmt, Seq())
    }
  }

  def addOldIfNecessary(head: Exp): Exp = {
    head match {
      case unfold: Unfolding => Old(unfold)(unfold.pos)
      case default => default
    }
  }

  //conjuction = true => Or
  //conjuction = false => And
  def buildDecTree(decrFuncS: Seq[Exp], conj: Boolean): Exp = {
    if (decrFuncS.size == 1)
      decrFuncS.head
    else if (conj)
      Or(decrFuncS.head, buildDecTree(decrFuncS.tail, conj = false))(decrFuncS.head.pos)
    else
      And(decrFuncS.head, buildDecTree(decrFuncS.tail, conj = true))(decrFuncS.head.pos)
  }

  def buildBoundTree(decrFuncS: Seq[Exp]): Exp = {
    if (decrFuncS.size == 1)
      decrFuncS.head
    else
      And(decrFuncS.head, buildBoundTree(decrFuncS.tail))(decrFuncS.head.pos)
  }

}