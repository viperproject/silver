/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.verifier.errors.{AssertFailed, TerminationFailed}
import viper.silver.verifier.reasons._

/** Utility methods for DecreaseClauses. */
object DecreasesClause {


  var decreasingFunc: DomainFunc = _
  //= DomainFunc("decreasing", Seq(LocalVarDecl("arg1", TypeVar("T1"))(NoPosition), LocalVarDecl("arg2", TypeVar("T2"))(NoPosition)), Bool, false)(NoPosition, NoInfo, "")
  var boundedFunc: DomainFunc = _
  //= DomainFunc("bounded", Seq(LocalVarDecl("arg1", TypeVar("T1"))(NoPosition)), Bool, false)(NoPosition, NoInfo, "")
  var nestedFunc: DomainFunc = _
  //= DomainFunc("nested", Seq(LocalVarDecl("arg1", TypeVar("T1"))(NoPosition), LocalVarDecl("arg2", TypeVar("T2"))(NoPosition)), Bool, false)(NoPosition, NoInfo, "")
  var locationDomain: Domain = _ //= Domain("locDomain", Nil, Nil, Nil)(NoPosition)


  var createdDomains: Seq[Domain] = Nil
  var neededLocalVars: Seq[LocalVarDecl] = Nil

  var dummyFunctions: Map[Function, Function] = Map()

  def addDummyFunctions(funcs: Seq[Function]): Seq[Function] = {
    funcs.foreach(
      f => dummyFunctions += (f -> Function(f.name + "_withoutBody", f.formalArgs, f.typ, f.pres, Nil, None, None)(f.pos))
    )
    dummyFunctions.values.toSeq
  }

  //TODO
  // multiple function calls -> multiple assertions
  def addMethods(funcs: Seq[Function], preds: Seq[Predicate], decFunc: Option[Node], boundFunc: Option[Node], nestFunc: Option[Node], locDom: Option[Node], findFnc: (String) => Function): (Seq[Domain], Seq[Function], Seq[Method]) = {

    val neededDomains = addDomains(preds, locDom)
    val neededDummyFncs = addDummyFunctions(funcs)

    decFunc match {
      case Some(decF) => decreasingFunc = decF.asInstanceOf[DomainFunc]
      case None =>
    }
    boundFunc match {
      case Some(boundF) => boundedFunc = boundF.asInstanceOf[DomainFunc]
      case None =>
    }
    nestFunc match {
      case Some(nestF) => nestedFunc = nestF.asInstanceOf[DomainFunc]
      case None =>
    }

    //Create for every Function a method which proofs the termination
    val methods = funcs map { func =>
      ///LOG
      println("DecClauses: ")
      func.decs match {
        case Some(DecStar()) => println("*")
        case Some(DecTuple(e)) => println(e)
        case d =>
      }
      ////

      val m = Method(func.name + "_termination_proof", func.formalArgs, Seq(), func.pres, Nil, Nil, Statements.EmptyStmt)(NoPosition, func.info, func.errT)

      func.body match {
        case Some(body) =>

          //Create the body of the proof method
          val newBody: Stmt = rewriteFuncBody(body, body, canReturn = true, func, Set(), findFnc, preds)

          //Replace every Function with the corresponding "dummy"-Function with no body, to prevent using wrong triggers
          val allUsedFncApps = newBody.deepCollect {
            case f: FuncApp => f
          }
          val dummyFncApps: Seq[FuncApp] = allUsedFncApps map (fa => FuncApp(dummyFunctions(findFnc(fa.funcname)), fa.args)(fa.pos, fa.info, fa.errT))
          m.body = newBody.replace((allUsedFncApps zip dummyFncApps).toMap)

        case None => //no termination check
      }
      m.locals = neededLocalVars
      m
    }
    (neededDomains, neededDummyFncs, methods)
  }


  def addDomains(predicates: Seq[Predicate], locDom: Option[Node]): Seq[Domain] = {

    //TODO store these Domains local
    locDom match {
      case Some(dom) =>
        val locDomain = dom.asInstanceOf[Domain]
        assert(locDomain.typVars.size == 1)
        assert(locDomain.functions.isEmpty)
        //Add necessary functions in the domain Loc[T]
        //Add a function for each signature of predicate into the Location Domain
        predicates.foreach { p =>
          val funcName: String = "loc_" + p.formalArgs.map(_.typ).mkString("_")
          //if signature not already added
          locDomain.functions.find(_.name == funcName) match {
            case Some(_) => //Already added
            case None => locDomain.functions :+= DomainFunc(funcName, p.formalArgs, DomainType(locDomain, Map(locDomain.typVars.head -> locDomain.typVars.head)), unique = false)(locDomain.pos, locDomain.info, locDomain.name, locDomain.errT)
          }
        }
        locationDomain = locDomain
        ////////////////////////////////////////////////
        //Add necessay Domains
        createdDomains = predicates map { pred =>
          Domain(pred.name + "_PredName", Seq(), Seq(), Seq())(NoPosition) //pege TODO Position?
        }
        createdDomains
      case None => Seq() //No Location Domain
    }
  }

  def rewriteFuncBody(bodyToRewrite: Exp, origBody: Exp, canReturn: Boolean, func: Function, alreadyChecked: Set[String], findFnc: (String) => Function, predicates: Seq[Predicate]): Stmt = {

    //TODO find instead filter
    //TODO replace
    bodyToRewrite match {
      case p: AccessPredicate => p match {
        case FieldAccessPredicate(loc, perm) => Statements.EmptyStmt //important?
        case pap: PredicateAccessPredicate =>
          val pred: Predicate = predicates.filter(_.name == pap.loc.predicateName).head //predicates use of?

          pred.body match {
            case Some(body) =>
              val res = rewritePredBodyAsExp(body, pap)
              neededLocalVars = res._2
              res._1
            case None => Statements.EmptyStmt
          }

      }
      case CondExp(cond, thn, els) =>
        cond match {
          case conj: And =>
            //Check Termination in the left condition of the conjuction
            val checkTermInleftCond: Stmt = rewriteFuncBody(conj.left, origBody, canReturn, func, alreadyChecked, findFnc, predicates)
            var checkTermInRightCond = rewriteFuncBody(CondExp(conj.right, thn, els)(cond.pos), origBody, canReturn, func, alreadyChecked, findFnc, predicates)

            conj.right match {
              case _: And | _: Or => checkTermInRightCond match {
                case s: Seqn => checkTermInRightCond = Seqn(s.ss.dropRight(1))(s.pos)
                case _ =>
              }
              case _ =>
            }
            //val wholeCond : Stmt = If(conj.left, leftCondTrue, rewriteFuncBodyAsStmts(els, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates))(cond.pos)
            val conditonForTermChecks: Stmt = If(conj.left, checkTermInRightCond, Statements.EmptyStmt)(cond.pos)
            val checkBody = If(cond, rewriteFuncBody(thn, origBody, canReturn = false, func, alreadyChecked, findFnc, predicates), rewriteFuncBody(els, origBody, canReturn, func, alreadyChecked, findFnc, predicates))(bodyToRewrite.pos)
            Seqn(Seq(checkTermInleftCond, conditonForTermChecks, checkBody))(bodyToRewrite.pos)
          case disj: Or =>
            val checkTermInleftCond: Stmt = rewriteFuncBody(disj.left, origBody, canReturn, func, alreadyChecked, findFnc, predicates)
            var checkTermInRightCond = rewriteFuncBody(CondExp(disj.right, thn, els)(cond.pos), origBody, canReturn, func, alreadyChecked, findFnc, predicates)

            disj.right match {
              case _: And | _: Or => checkTermInRightCond match {
                case s: Seqn => checkTermInRightCond = Seqn(s.ss.dropRight(1))(s.pos)
                case _ =>
              }
              case _ =>
            }
            //val wholeCond : Stmt = If(disj.left, rewriteFuncBodyAsStmts(thn, decreasingFunc, boundedFunc, nestedFunc, locDmain, func, alreadyChecked, findFnc, predicates), leftCondFalse)(cond.pos)
            val conditonForTermChecks: Stmt = If(Not(disj.left)(cond.pos), checkTermInRightCond, Statements.EmptyStmt)(cond.pos)

            val checkBody = If(cond, rewriteFuncBody(thn, origBody, canReturn = false, func, alreadyChecked, findFnc, predicates), rewriteFuncBody(els, origBody, canReturn, func, alreadyChecked, findFnc, predicates))(bodyToRewrite.pos)
            Seqn(Seq(checkTermInleftCond, conditonForTermChecks, checkBody))(bodyToRewrite.pos)
          case _ =>
            val checkTermInCond = rewriteFuncBody(cond, origBody, canReturn = false, func, alreadyChecked, findFnc, predicates)
            val thnSt = rewriteFuncBody(thn, origBody, canReturn, func, alreadyChecked, findFnc, predicates)
            val elsSt = rewriteFuncBody(els, origBody, canReturn, func, alreadyChecked, findFnc, predicates)
            val wholeCond = If(cond, thnSt, elsSt)(bodyToRewrite.pos)
            Seqn(Seq(checkTermInCond, wholeCond))(bodyToRewrite.pos)
        }
      case Unfolding(acc, unfBody) =>
        val s1 = Unfold(acc)(unfBody.pos)
        val s2 = rewriteFuncBody(acc, origBody, canReturn = false, func, alreadyChecked, findFnc, predicates)
        val s3 = rewriteFuncBody(unfBody, origBody, canReturn, func, alreadyChecked, findFnc, predicates)
        val s4 = Fold(acc)(unfBody.pos)
        Seqn(Seq(s1, s2, s3, s4))(unfBody.pos)



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

        val dec = func.decs

        //If no decreasing argument is given, try to proof termination by decreasing the first argument
        //        if (decClause.isEmpty) {
        //          decClause = Seq(LocalVar(func.formalArgs.head.name)(func.formalArgs.head.typ))
        //        }

        val calleeArgs = callee.getArgs
        val termCheckOfArgs = calleeArgs map (rewriteFuncBody(_, origBody, canReturn = false, func, alreadyChecked, findFnc, predicates))


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
                  case _: AssertionFalse => CallingNonTerminatingFunction(bodyToRewrite, func.name, callee.funcname)
                  case k => k
                })
                })

                Seqn(termCheckOfArgs ++ Seq(Assert(FalseLit()(func.pos))(pos = func.pos, info = SimpleInfo(Seq("Called Fnc (" + callee.funcname + ") does not terminate")), errT = errTr)))(bodyToRewrite.pos)

              case _ =>
                //search for a recursion in the called function
                val newFormalArgs = callee.formalArgs map {
                  case l: LocalVarDecl => LocalVar(l.name)(l.typ) //, l.pos, l.info, l.errT)
                  case a => a
                }

                var body = newFunc.body.get //TODO what if no body
                //body = body.replace((newFormalArgs.asInstanceOf[Seq[Exp]] zip calleeArgs).toMap)
                body = body.replace((newFormalArgs zip calleeArgs).toMap)
                val termCheckOfFuncBody = rewriteFuncBody(body, origBody, canReturn = false, func, alreadyChecked ++ Set(callee.funcname), findFnc, predicates)

                //if bodyToRewrite inside origBody then inhale...
                if (origBody.hasSubnode(bodyToRewrite)) { //we are in the first called function
                  val formalArgs = func.formalArgs map {
                    varDecl => LocalVar(varDecl.name)(varDecl.typ, varDecl.pos, varDecl.info, varDecl.errT)
                  }
                  //val assumption = Inhale(EqCmp(Old(FuncApp(func, calleeArgs)(body.pos))(body.pos), body)(body.pos))(body.pos)
                  val assumption = Inhale(EqCmp(FuncApp(func, calleeArgs)(body.pos), body)(body.pos))(body.pos)
                  Seqn(termCheckOfArgs ++ Seq(termCheckOfFuncBody, assumption))(body.pos) //TODO Position?
                } else {
                  Seqn(termCheckOfArgs ++ Seq(termCheckOfFuncBody))(body.pos)
                }
            }
          } else {
            Seqn(termCheckOfArgs)(bodyToRewrite.pos)
          }

        } else {
          //Called Function is the same as the original one => recursion detected

          if (dec.isEmpty) { //TODO isDefined or isEmpty?
            //There is a decrease Clause //TODO no decClause size=0
            //Give an error, because you have recursion but no decreases clause
            println("Error - There is recursion but no decClause defined - " + func.name)

            val errTr = ErrTrafo({ case AssertFailed(_, r) => TerminationFailed(callee, r match {
              case _: AssertionFalse => NoDecClauseSpecified(bodyToRewrite, callee.funcname)
              case k => k
            })
            })

            Assert(FalseLit()(func.pos))(pos = func.pos, info = SimpleInfo(Seq("Recursion but no decClause")), errT = errTr)
          }
          else {
            //Replace in the decreaseClause every argument with the correct call
            //TODO are there other AccessPredicate?
            dec match {
              case Some(DecTuple(decClause)) =>

                //Cast Arguments to LocalVariables
                val formalArgs: Seq[LocalVar] = func.formalArgs map {
                  varDecl => LocalVar(varDecl.name)(varDecl.typ, varDecl.pos, varDecl.info, varDecl.errT)
                }

                val smallerExpression: Seq[Exp] = decClause map {
                  case pred: PredicateAccessPredicate =>
                    LocalVar(getPredVarName(pred.loc.predicateName, calleeArgs))(getPredVarType(pred.loc.predicateName))
                  case decC => decC.replace((formalArgs zip calleeArgs).toMap)
                }
                val biggerExpression: Seq[Exp] = decClause map {
                  case pred: PredicateAccessPredicate =>
                    LocalVar(getPredVarName(pred.loc.predicateName, formalArgs))(getPredVarType(pred.loc.predicateName))
                  case d => addOldIfNecessary(d)
                }

                val pos = bodyToRewrite.pos
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
                  decrFunc :+= DomainFuncApp(decreasingFunc, Seq(e(i)._1, e(i)._2), Map(argTypeVarsDecr.head -> e(i)._1.typ, argTypeVarsDecr.last -> e(i)._2.typ))(decreasingFunc.pos)
                  boundFunc :+= DomainFuncApp(boundedFunc, Seq(e(i)._1), Map(argTypeVarsDecr.head -> e(i)._1.typ))(boundedFunc.pos)
                }

                val boundedAss = Assert(buildBoundTree(boundFunc))(pos, infoBound, errTBound)
                val decreaseAss = Assert(buildDecTree(decrFunc, conj = true))(pos, infoDecr, errTDecr) //TODO mapDecr

                //if(bodyToRewrite == )
                //replace((formalArgs zip calleeArgs).toMap)
                if (origBody.hasSubnode(bodyToRewrite)) { //we are in the first called function
                  val assumption =  Inhale(EqCmp(FuncApp(func, calleeArgs)(pos), origBody.replace((formalArgs zip calleeArgs).toMap))(pos))(pos)
                  //val assumption = Inhale(EqCmp(Old(FuncApp(func, calleeArgs)(pos))(pos), origBody.replace((formalArgs zip calleeArgs).toMap))(pos))(pos)
                  Seqn(termCheckOfArgs ++ Seq(boundedAss, decreaseAss, assumption))(pos) //TODO Position?
                } else {
                  Seqn(termCheckOfArgs ++ Seq(boundedAss, decreaseAss))(pos) //TODO Position?
                }

              case Some(DecStar()) =>
                //Do Nothing -> Users says that function will not terminate
                Statements.EmptyStmt
              case None => Statements.EmptyStmt
            }
          }
        }

      case b: BinExp =>
        //TODO rewrite
        val left = rewriteFuncBody(b.left, origBody, canReturn = false, func, alreadyChecked, findFnc, predicates)
        val right = rewriteFuncBody(b.right, origBody, canReturn = false, func, alreadyChecked, findFnc, predicates)
        if (canReturn) {
          val formalArgs = func.formalArgs map {
            varDecl => LocalVar(varDecl.name)(varDecl.typ, varDecl.pos, varDecl.info, varDecl.errT)
          }
          val ass = Inhale(EqCmp(Old(FuncApp(func, formalArgs)(b.pos))(b.pos), b)(b.pos))(b.pos)
          //val ass = Inhale(EqCmp(FuncApp(func, formalArgs)(b.pos), b)(b.pos))(b.pos)
          Seqn(Seq(left, right, ass))(b.pos)
        } else {
          Seqn(Seq(left, right))(b.pos)
        }
      case u: UnExp => rewriteFuncBody(u.exp, origBody, canReturn = false, func, alreadyChecked, findFnc, predicates)

      //      case _: Literal | _: GhostOperation | _: Let | _: QuantifiedExp | _: AbstractLocalVar | _: SeqExp | _: SetExp | _: MultisetExp
      //      | _: InhaleExhaleExp | _: PermExp | _: LocationAccess | _: Lhs | _: ForbiddenInTrigger | _: FuncLikeApp =>
      case rest: Exp =>
        if (canReturn) {
          val formalArgs = func.formalArgs map {
            varDecl => LocalVar(varDecl.name)(varDecl.typ, varDecl.pos, varDecl.info, varDecl.errT)
          }
          Inhale(EqCmp(Old(FuncApp(func, formalArgs)(rest.pos))(rest.pos), rest)(rest.pos))(rest.pos)
          //Inhale(EqCmp(FuncApp(func, formalArgs)(rest.pos), rest)(rest.pos))(rest.pos)
        } else {
          Statements.EmptyStmt
        }
    }
  }

  def rewritePredBodyAsExp(body: Exp, origPred: PredicateAccessPredicate): (Stmt, Seq[LocalVarDecl]) = {
    body match {
      case predi: AccessPredicate => predi match {
        case FieldAccessPredicate(loc, perm) => (Statements.EmptyStmt, Seq())
        case calledPred: PredicateAccessPredicate =>

          //TODO find instead of filter equal
          getPredVarType(origPred.loc.predicateName)

          val domainOfCallerPred: Domain = getPredDomain(origPred.loc.predicateName)
          val domainOfCalleePred: Domain = getPredDomain(calledPred.loc.predicateName)

          //          //TODO subExps not good (1+(1+i))
          //          val callerPredName = origPred.loc.predicateName + "_" + origPred.loc.args.map(_.toString()).mkString("_").replace(".", ""))
          //          val calleePredName = calledPred.loc.predicateName + "_" + calledPred.loc.args.map(_.toString()).mkString("_").replace(".", ""))
          val callerPredName = getPredVarName(origPred.loc.predicateName, origPred.loc.args)
          val calleePredName = getPredVarName(calledPred.loc.predicateName, calledPred.loc.args)

          val varOfCallerPred = LocalVar(callerPredName)(getPredVarType(origPred.loc.predicateName), calledPred.pos)
          val varOfCalleePred = LocalVar(calleePredName)(getPredVarType(calledPred.loc.predicateName), calledPred.pos)

          val varDeclCallerPred: LocalVarDecl = LocalVarDecl(varOfCallerPred.name, varOfCallerPred.typ)(varOfCallerPred.pos)
          val varDeclCalleePred: LocalVarDecl = LocalVarDecl(varOfCalleePred.name, varOfCalleePred.typ)(varOfCalleePred.pos)

          //TODO method generateSignature()
          val funcNameCaller: String = "loc_" + origPred.loc.args.map(_.typ).mkString("_")
          val funcNameCallee: String = "loc_" + calledPred.loc.args.map(_.typ).mkString("_")

          val domainFuncOut: DomainFunc = locationDomain.functions.filter(_.name == funcNameCaller).head
          val mapOut: Map[TypeVar, Type] = Map(TypeVar(locationDomain.typVars.head.name) -> DomainType(domainOfCallerPred, Map()))
          val outSideFunc = DomainFuncApp(domainFuncOut, origPred.loc.args, mapOut)(calledPred.pos)
          val assign1 = LocalVarAssign(varOfCallerPred, outSideFunc)(calledPred.pos)

          val domainFuncIn = locationDomain.functions.filter(_.name == funcNameCallee).head
          val mapIn: Map[TypeVar, Type] = Map(TypeVar(locationDomain.typVars.head.name) -> DomainType(domainOfCalleePred, Map()))
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
        val thn = rewritePredBodyAsExp(c.thn, origPred)
        val els = rewritePredBodyAsExp(c.els, origPred)
        (If(c.cond, thn._1, els._1)(c.pos), thn._2 ++ els._2)
      case b: BinExp =>
        val left = rewritePredBodyAsExp(b.left, origPred)
        val right = rewritePredBodyAsExp(b.right, origPred)
        (Seqn(Seq(left._1, right._1))(b.pos), left._2 ++ right._2)
      case u: UnExp => rewritePredBodyAsExp(u.exp, origPred)
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

  def getPredVarName(predName: String, args: Seq[Exp]) : String = {
    //predName + "_" + (args.mkString.replaceAll("[^A-Za-z0-9]+", ""))
    predName + "_" + args.hashCode().toString.replaceAll("-", "_")
  }

  def getPredVarType(predName: String) : Type = {
    DomainType(locationDomain, Map(TypeVar(locationDomain.typVars.head.name) -> DomainType(getPredDomain(predName), Map())))
  }

  def getPredDomain(predName: String) : Domain = {
    createdDomains.find(_.name == (predName + "_PredName")).head
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