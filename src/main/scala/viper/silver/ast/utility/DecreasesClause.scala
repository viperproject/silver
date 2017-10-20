/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.FastMessaging
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{StrategyBuilder, Traverse}
import viper.silver.verifier.errors.{AssertFailed, TerminationFailed}
import viper.silver.verifier.reasons._
import viper.silver.ast.utility.Statements.EmptyStmt

import scala.collection.immutable.ListMap

/** Utility methods for DecreaseClauses. */
class DecreasesClause(val members: collection.mutable.HashMap[String, Node]) {

  private var decreasingFunc: Option[DomainFunc] = None
  private var boundedFunc: Option[DomainFunc] = None
  private var nestedFunc: Option[DomainFunc] = None
  private var locationDomain: Option[Domain] = None

  private var neededLocalVars = collection.mutable.ListMap[String, LocalVarDecl]()
  private val neededDummyFncs = collection.mutable.ListMap[String, Function]()
  private val neededLocFunctions = collection.mutable.ListMap[String, DomainFunc]()
  private val neededPredDomains = collection.mutable.ListMap[String, Domain]()

  private def findFnc(name: String) = members(name).asInstanceOf[Function]


  /**
    * Adds to a given program for every function a method, which can be used for verifying the termination of that
    * function. The methods will be constructed around a given decreases-clause and will return corresponding
    * error messages.
    *
    * @param funcs     all existing functions in a program
    * @param preds     all existing predicates in a program
    * @param doms      all existing domains in a program
    * @param decFunc   the decreasing function. It takes two arguments and defines when a value is strictly "smaller"
    *                  than another. It is used for proving decreasing values.
    * @param boundFunc the bounded Function. It takes one argument and defines if a value is bounded.
    * @param nestFunc  the nested Function. It takes two predicates as arguments, and defines when one predicate is
    *                  "inside" another one
    * @param locDom    the location Domain. It is used to define a typ "Predicate", for showing decreasing predicates
    * @return The necessary components (functions, methods, domains), which should be added in a viper program
    *         such that termination of functions can be verified
    */
  def addMethods(funcs: Seq[Function],
                 preds: Seq[Predicate],
                 doms: Seq[Domain],
                 decFunc: Option[Node],
                 boundFunc: Option[Node],
                 nestFunc: Option[Node],
                 locDom: Option[Node])
                : (Seq[Domain], Seq[Function], Seq[Method]) = {

    decreasingFunc = decFunc map (_.asInstanceOf[DomainFunc])
    boundedFunc = boundFunc map (_.asInstanceOf[DomainFunc])
    locationDomain = locDom map (_.asInstanceOf[Domain])
    nestedFunc = nestFunc map (_.asInstanceOf[DomainFunc])

    //Create for every Function a method which proofs the termination
    //Ignore functions with 'decreases *' or with no body
    val methods = (funcs.filter(f => f.body.nonEmpty && (f.decs.isEmpty || !f.decs.get.isInstanceOf[DecStar])) map {
      func => {
        neededLocalVars = collection.mutable.ListMap.empty[String, LocalVarDecl]
        val methodBody: Stmt = rewriteFuncBody(func.body.get, func, null, Nil, preds)

        val methodName = uniqueName(func.name + "_termination_proof")

        val newMethodBody = Seqn(Seq(methodBody), neededLocalVars.values.toIndexedSeq)(methodBody.pos)

        val newMethod = Method(methodName, func.formalArgs, Seq(), func.pres, Nil, Some(newMethodBody))(NoPosition, func.info, func.errT)
        members(methodName) = newMethod
        newMethod
    }}).filter(_.body.getOrElse(Seq.empty).collect{case k: Assert => k}.nonEmpty)

    if (neededLocFunctions.nonEmpty) {
      assert(locationDomain.isDefined)
      val domainsWLoc = doms.filterNot(_ == locationDomain.get)
      val newLocDom = Domain(locationDomain.get.name,
        neededLocFunctions.values.toSeq,
        locationDomain.get.axioms,
        locationDomain.get.typVars)(locationDomain.get.pos, locationDomain.get.info, locationDomain.get.errT)
      (domainsWLoc ++ Seq(newLocDom) ++ neededPredDomains.values.toSeq, neededDummyFncs.values.toSeq, methods)
    } else {
      (doms ++ neededPredDomains.values.toSeq, neededDummyFncs.values.toSeq, methods)
    }
  }

  /**
    * Transforms the body of a function into statements, such that the termination of (direct or indirect) recursions
    * can be verified.
    * The method stores needed domains, functions and local variables in global fields
    *
    * @param bodyToRewrite     expression which will be transformed to statements
    * @param func              original function
    * @param funcAppInOrigFunc is the position where the original function calls another function.
    *                          It is used for ErrorMeassges
    * @param alreadyChecked    set of functions which has been already traversed, to hinder infinity checks
    * @param predicates        set of all predicates, used in proof generation for decreasing predicates
    * @return a (sequence of) statement, which can be used for verifying termination of a given expression
    */
  private def rewriteFuncBody(bodyToRewrite: Exp,
                              func: Function,
                              funcAppInOrigFunc: FuncApp,
                              alreadyChecked: Seq[String],
                              predicates: Seq[Predicate])
                              : Stmt = {
    bodyToRewrite match {
      case pap: PredicateAccessPredicate =>
        val permChecks = rewriteFuncBody(pap.perm, func, funcAppInOrigFunc, alreadyChecked, predicates)
        //Add the nested-assumption if the predicate has another predicate inside of its body
        func.decs match {
          case Some(DecTuple(_)) =>
            val pred: Predicate = predicates.find(_.name == pap.loc.predicateName).get

            pred.body match {
              case Some(body) =>
                if (locationDomain.isDefined && nestedFunc.isDefined) {
                  val formalArgs = pred.formalArgs map (_.localVar)
                  //Generate nested-assumption
                  val predBody = rewritePredBodyAsExp(body.replace(ListMap(formalArgs.zip(pap.loc.args):_*)), pap)
                  Seqn(Seq(permChecks, predBody), Nil)(body.pos)
                } else {
                  if (locationDomain.isEmpty) {
                    Consistency.messages ++= FastMessaging.message(
                      func, "missing location-domain")
                  }
                  if (nestedFunc.isEmpty) {
                    Consistency.messages ++= FastMessaging.message(
                      func, "missing nested-relation")
                  }
                  permChecks
                }
              //Predicate has no body
              case None => permChecks
            }
          //No decreasing clause
          case _ => permChecks
        }

      case CondExp(cond, thn, els) =>
        //Check for possible recursion inside of the condition
        val termCheckInCond = rewriteFuncBody(cond, func, funcAppInOrigFunc, alreadyChecked, predicates)
        val thnSt = rewriteFuncBody(thn, func, funcAppInOrigFunc, alreadyChecked, predicates)
        val elsSt = rewriteFuncBody(els, func, funcAppInOrigFunc, alreadyChecked, predicates)

        val wholeCond = if (thnSt == EmptyStmt && elsSt == EmptyStmt) EmptyStmt else {
          If(replaceExpWithDummyFnc(cond), Seqn(Seq(thnSt), Nil)(bodyToRewrite.pos),
            Seqn(Seq(elsSt), Nil)(bodyToRewrite.pos))(bodyToRewrite.pos)
        }
        Seqn(Seq(termCheckInCond, wholeCond), Nil)(bodyToRewrite.pos)
      case Unfolding(acc, unfBody) =>
        val unfold = Unfold(acc)(unfBody.pos)
        val access = rewriteFuncBody(acc, func, funcAppInOrigFunc, alreadyChecked, predicates)
        val unfoldBody = rewriteFuncBody(unfBody, func, funcAppInOrigFunc, alreadyChecked, predicates)
        val fold = Fold(acc)(unfBody.pos)

        unfoldBody match {
          case EmptyStmt => EmptyStmt
          case _ => Seqn(Seq(unfold, access, unfoldBody, fold), Nil)(unfBody.pos)
        }
      case callee: FuncApp =>
        val decrClauseOfOrigFnc = func.decs
        val calleeArgs = callee.getArgs

        //Check for possible recursion inside of the arguments
        val termChecksOfArgs = calleeArgs map (rewriteFuncBody(_, func, funcAppInOrigFunc, alreadyChecked, predicates))

        if (callee.funcname != func.name) {
          //Called function is not the original function => no recursion so far
          if (!alreadyChecked.contains(callee.funcname)) {
            //Program didn't check this function for recursion yet
            val calledFunc = findFnc(callee.funcname)

            calledFunc.decs match {
              case Some(DecStar()) =>
                //The called function might not terminate
                val functionInOrigBody = if (funcAppInOrigFunc == null) callee else funcAppInOrigFunc

                val errTr = ErrTrafo({ case AssertFailed(_, _, _) => TerminationFailed(
                  func,
                  CallingNonTerminatingFunction(functionInOrigBody, calledFunc)) })
                val info = SimpleInfo(Seq("Called Fnc (" + callee.funcname + ") does not terminate"))
                Seqn(termChecksOfArgs ++ Seq(Assert(FalseLit()(func.pos))(pos = func.pos, info, errT = errTr)),
                  Nil)(bodyToRewrite.pos)

              case _ =>
                //Check the called unction for recursion

                val formalArgsOfCallee = calledFunc.formalArgs map (_.localVar)

                //Arguments are now checked -> to not check same recursions again, replace them with their dummyFnc
                val mapFormalArgsToCalledArgs = ListMap(formalArgsOfCallee.zip(calleeArgs map replaceExpWithDummyFnc):_*)

                if (calledFunc.body.nonEmpty) {
                  val body = calledFunc.body.get.replace(mapFormalArgsToCalledArgs)
                  val pos = body.pos

                  //Check for recursion in the new function-body
                  val termCheckOfFuncBody = rewriteFuncBody(
                    body,
                    func,
                    if (funcAppInOrigFunc == null) callee else funcAppInOrigFunc,
                    alreadyChecked ++ Seq(callee.funcname),
                    predicates)

                  //Replace 'result' in the postconditions with the function and the correct arguments
                  val resNodes = calledFunc.posts flatMap (p => p.deepCollect { case r: Result => r })
                  val resMap = ListMap(resNodes.zip(List.fill(resNodes.size)(FuncApp(calledFunc, calleeArgs)(pos))):_*)
                  val postConds: Seq[Exp] = calledFunc.posts map (p => p.replace(mapFormalArgsToCalledArgs ++ resMap))

                  val inhalePostConds = postConds map (c => Inhale(replaceExpWithDummyFnc(c))(pos))

                  val inhaleFuncBody =
                    Inhale(replaceExpWithDummyFnc(EqCmp(FuncApp(calledFunc, calleeArgs)(pos), body)(pos)))(pos)
                  Seqn(termChecksOfArgs ++ Seq(termCheckOfFuncBody, inhaleFuncBody) ++ inhalePostConds, Nil)(pos)
                } else {
                  //Function has no body
                  //Replace 'result' in the postconditions with the function and the correct arguments
                  val resNodes = calledFunc.posts flatMap (p => p.deepCollect { case r: Result => r })
                  val resMap =
                    ListMap(resNodes.zip(List.fill(resNodes.size)(FuncApp(calledFunc, calleeArgs)(bodyToRewrite.pos))):_*)
                  val postConds: Seq[Exp] = calledFunc.posts map (p => p.replace(mapFormalArgsToCalledArgs ++ resMap))

                  val inhalePostConds = postConds map (c => Inhale(replaceExpWithDummyFnc(c))(bodyToRewrite.pos))
                  Seqn(termChecksOfArgs ++ inhalePostConds, Nil)(bodyToRewrite.pos)
                }
            }
          } else {
            //Program already checked this function for recursion
            Seqn(termChecksOfArgs, Nil)(bodyToRewrite.pos)
          }
        } else {
          //Called function is the same as the original one => recursion detected
          decrClauseOfOrigFnc match {
            case None => {
            //There is no decrease clause
            //Give an error, because there is a recursion but no decreases clause
            val functionInOrigBody = if (funcAppInOrigFunc == null) callee else funcAppInOrigFunc
            val errTr =
              ErrTrafo({case AssertFailed(_, _, _) => TerminationFailed(func, NoDecClauseSpecified(functionInOrigBody))})

            Assert(FalseLit()(func.pos))(func.pos, SimpleInfo(Seq("Recursion but no decClause")), errTr)
            }
            case Some(DecTuple(decreasingExp)) => {
            //Replace in the decreaseClause every argument with the correct call
                if (decreasingFunc.isDefined && boundedFunc.isDefined &&
                   (decreasingExp.collect { case p: PredicateAccessPredicate => p }.isEmpty
                    || locationDomain.isDefined)) {

                  val formalArgs: Seq[LocalVar] = func.formalArgs map (_.localVar)

                  var neededArgAssigns: Seq[Stmt] = Nil //Needed for decreasing predicates

                  //Decreasing(smallerExpr, biggerExpr) <==> smallerExpr '<<' biggerExpr
                  val smallerExpression: Seq[Exp] = decreasingExp map {
                    case pap: PredicateAccessPredicate =>
                      val argMap: ListMap[Exp,Exp] = ListMap(formalArgs.zip(calleeArgs): _*)
                      val varOfCalleePred = uniquePredLocVar(pap.loc, argMap)

                      neededArgAssigns :+= generateAssign(pap, varOfCalleePred, argMap)
                      varOfCalleePred
                    case decC => decC.replace(ListMap(formalArgs.zip(calleeArgs):_*))
                  }

                  val biggerExpression: Seq[Exp] = decreasingExp map {
                    case pap: PredicateAccessPredicate =>
                      assert(locationDomain.isDefined)
                      val varOfCalleePred = uniquePredLocVar(pap.loc)

                      neededArgAssigns :+= generateAssign(pap, varOfCalleePred)
                      varOfCalleePred
                    case d => d match {
                      case unfold: Unfolding => Old(unfold)(unfold.pos)
                      case default => default
                    }
                  }

                  val pos = bodyToRewrite.pos
                  val infoBound = SimpleInfo(Seq("BoundedCheck"))
                  val infoDecr = SimpleInfo(Seq("DecreasingCheck"))

                  val callerFunctionInOrigBody = if (funcAppInOrigFunc == null) callee else funcAppInOrigFunc

                  //Map AssertionErrors to TerminationFailedErrors
                  val errTBound = ErrTrafo({ case AssertFailed(_, reason, _) => TerminationFailed(func, reason match {
                    case AssertionFalse(offendingNode) => offendingNode match {
                      case dfa: DomainFuncApp =>
                        assert(dfa.args.size == 1)
                        TerminationNoBound(DecTuple(decreasingExp)(callerFunctionInOrigBody.pos), dfa.args.head match {
                          case PredicateAccessPredicate(loc, _) => loc
                          case d => d
                        })
                      case _ => reason
                    }
                  })
                  })

                  //Map AssertionErrors to TerminationFailedErrors
                  val errTDecr = ErrTrafo({ case AssertFailed(_, reason, _) => TerminationFailed(func, reason match {
                    case AssertionFalse(_) =>
                      VariantNotDecreasing(callerFunctionInOrigBody, decreasingExp map {
                        case p: PredicateAccessPredicate => p.loc
                        case r => r
                      })
                    case d => d
                  })
                  })

                  val argsForTermProof = smallerExpression zip biggerExpression

                  val paramTypesDecr = decreasingFunc.get.formalArgs map (_.typ)
                  val argTypeVarsDecr = paramTypesDecr.flatMap(p => p.typeVariables)

                  var decrFunc: Seq[Exp] = Nil
                  var boundFunc: Seq[Exp] = Nil

                  //Generation of termination Assertions - (Assert decreasing(..,..))
                  //Generates (for a decreasing Clause: 'decreases a,b,c') a sequence with the following form:
                  //(dec(a,a), a==a, dec(b,b), b==b, dec(c,c))
                  for (i <- argsForTermProof.indices) {
                    if (i > 0) {
                      decrFunc :+= EqCmp(argsForTermProof(i - 1)._1, argsForTermProof(i - 1)._2)(decreasingFunc.get.pos)
                    }
                    decrFunc :+=
                      replaceExpWithDummyFnc(
                        DomainFuncApp(decreasingFunc.get,
                          Seq(argsForTermProof(i)._1, argsForTermProof(i)._2),
                          ListMap(argTypeVarsDecr.head -> argsForTermProof(i)._1.typ,
                            argTypeVarsDecr.last -> argsForTermProof(i)._2.typ))(callerFunctionInOrigBody.pos)
                      )
                    boundFunc :+= replaceExpWithDummyFnc(
                      DomainFuncApp(boundedFunc.get,
                        Seq(argsForTermProof(i)._1),
                        ListMap(argTypeVarsDecr.head -> argsForTermProof(i)._1.typ,
                          argTypeVarsDecr.last -> argsForTermProof(i)._2.typ))(callerFunctionInOrigBody.pos)
                    )

                  }

                  val boundedAss =
                    Assert(buildBoundTree(boundFunc))(callerFunctionInOrigBody.pos, infoBound, errTBound)
                  val decreaseAss =
                    Assert(buildDecTree(decrFunc, conj = true))(callerFunctionInOrigBody.pos, infoDecr, errTDecr)

                  if (funcAppInOrigFunc == null) {
                    //We are in the function we want to check

                    val argMap: ListMap[Exp, Exp] = ListMap(formalArgs.zip(calleeArgs):_*)
                    val bodyWithArgs = func.body.get.replace(argMap)

                    //Replace 'result' in the postconditions with the dummy-Function and the correct arguments
                    val resultNodes = func.posts flatMap (p => p.deepCollect { case r: Result => r })
                    val resMap = ListMap(resultNodes.zip(List.fill(resultNodes.size)(FuncApp(func, calleeArgs)(pos))):_*)
                    val postConds = func.posts map (p =>
                      p.replace(argMap ++ resMap))
                    val inhalePostConds = postConds map (c => Inhale(replaceExpWithDummyFnc(c))(pos))

                    val inhaleFuncBody =
                      Inhale(replaceExpWithDummyFnc(EqCmp(FuncApp(func, calleeArgs)(pos), bodyWithArgs)(pos)))(pos)

                    Seqn(termChecksOfArgs ++ neededArgAssigns ++
                      Seq(boundedAss, decreaseAss, inhaleFuncBody) ++ inhalePostConds, Nil)(pos)
                  } else {
                    Seqn(termChecksOfArgs ++ neededArgAssigns ++ Seq(boundedAss, decreaseAss), Nil)(pos)
                  }
                } else {
                  if (decreasingFunc.isEmpty) {
                    Consistency.messages ++= FastMessaging.message(func, "missing decreasing-function")
                  }
                  if (boundedFunc.isEmpty) {
                    Consistency.messages ++= FastMessaging.message(func, "missing bounded-function")
                  }
                  if (decreasingExp.collect {case p: PredicateAccessPredicate => p}.nonEmpty && locationDomain.isEmpty) {
                    Consistency.messages ++=
                      FastMessaging.message(func,
                                            "missing location-domain (needed for proving termination over predicates)")
                  }
                  EmptyStmt
                }
            }
            case res@Some(DecStar()) => {
              // Should never happen, because the function 'rewriteFuncBody(_, func, _, _, _)' should only be called
              // when the decreasing clause of the argument 'func' is not 'decreases *'
              sys.error(s"Got $res but this isn't supposed to happen")
            }
          }
        }
      case b: BinExp =>
        val left = rewriteFuncBody(b.left, func, funcAppInOrigFunc, alreadyChecked, predicates)
        val right = rewriteFuncBody(b.right, func, funcAppInOrigFunc, alreadyChecked, predicates)
        //Short circuit evaluation
        b match {
          case _: Or =>
            Seqn(Seq(left,
                    If(Not(replaceExpWithDummyFnc(b.left))(b.pos), Seqn(Seq(right), Nil)(b.pos), EmptyStmt)(b.pos)),
                Nil)(b.pos)
          case _: And =>
            Seqn(Seq(left,
                    If(replaceExpWithDummyFnc(b.left), Seqn(Seq(right), Nil)(b.pos), EmptyStmt)(b.pos)),
                Nil)(b.pos)
          case _: Implies =>
            Seqn(Seq(left,
                    If(replaceExpWithDummyFnc(b.left), Seqn(Seq(right), Nil)(b.pos), EmptyStmt)(b.pos)),
                Nil)(b.pos)
          case _ =>
            Seqn(Seq(left, right), Nil)(b.pos)
        }
      case sq: SeqExp => sq match {
        case ExplicitSeq(elems) =>
          Seqn(elems.map(rewriteFuncBody(_, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(sq.pos)
        case RangeSeq(low, high) =>
          Seqn(Seq(rewriteFuncBody(low, func, funcAppInOrigFunc, alreadyChecked, predicates),
                  rewriteFuncBody(high, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(sq.pos)
        case SeqAppend(left, right) =>
          Seqn(Seq(rewriteFuncBody(left, func, funcAppInOrigFunc, alreadyChecked, predicates),
            rewriteFuncBody(right, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(sq.pos)
        case SeqIndex(s, idx) =>
          Seqn(Seq(rewriteFuncBody(s, func, funcAppInOrigFunc, alreadyChecked, predicates),
            rewriteFuncBody(idx, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(sq.pos)
        case SeqTake(s, n) =>
          Seqn(Seq(rewriteFuncBody(s, func, funcAppInOrigFunc, alreadyChecked, predicates),
            rewriteFuncBody(n, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(sq.pos)
        case SeqDrop(s, n) =>
          Seqn(Seq(rewriteFuncBody(s, func, funcAppInOrigFunc, alreadyChecked, predicates),
            rewriteFuncBody(n, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(sq.pos)
        case SeqContains(elem, s) =>
          Seqn(Seq(rewriteFuncBody(elem, func, funcAppInOrigFunc, alreadyChecked, predicates),
            rewriteFuncBody(s, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(sq.pos)
        case SeqUpdate(s, idx, elem) =>
          Seqn(Seq(rewriteFuncBody(s, func, funcAppInOrigFunc, alreadyChecked, predicates),
            rewriteFuncBody(idx, func, funcAppInOrigFunc, alreadyChecked, predicates),
            rewriteFuncBody(elem, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(sq.pos)
        case SeqLength(s) =>
          Seqn(Seq(rewriteFuncBody(s, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(sq.pos)
        case _: Exp => EmptyStmt
      }
      case st: ExplicitSet =>
        Seqn(st.elems.map(rewriteFuncBody(_, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(st.pos)
      case mst: ExplicitMultiset =>
        Seqn(mst.elems.map(rewriteFuncBody(_, func, funcAppInOrigFunc, alreadyChecked, predicates)), Nil)(mst.pos)
      case u: UnExp => rewriteFuncBody(u.exp, func, funcAppInOrigFunc, alreadyChecked, predicates)
      case _: Exp => EmptyStmt
    }
  }

  /**
    * Traverses a predicate body and adds corresponding inhales of the 'nested'-Relation
    * iff a predicate is inside of this body
    *
    * @param body     the part of the predicate-body which should be analyzed
    * @param origPred the body of the original predicate which should be analyzed
    * @return statements with the generated inhales: (Inhale(nested(pred1, pred2)))
    */
  private def rewritePredBodyAsExp(body: Exp, origPred: PredicateAccessPredicate): Stmt = {

    body match {
      case ap: AccessPredicate => ap match {
        case FieldAccessPredicate(_, _) => EmptyStmt
        case calledPred: PredicateAccessPredicate =>
          assert(locationDomain.isDefined)
          assert(nestedFunc.isDefined)

          //predicate-Domains (p_PredName)
          val domainOfCallerPred: Domain = uniqueNameGen(origPred.loc).asInstanceOf[Domain]
          val domainOfCalleePred: Domain = uniqueNameGen(calledPred.loc).asInstanceOf[Domain]

          //local variables
          val varOfCallerPred: LocalVar = uniquePredLocVar(origPred.loc)
          val varOfCalleePred: LocalVar = uniquePredLocVar(calledPred.loc)

          //assign
          val assign1 = generateAssign(origPred, varOfCallerPred)
          val assign2 = generateAssign(calledPred, varOfCalleePred)

          //inhale nested-relation
          val params: Seq[TypeVar] = members(nestedFunc.get.domainName).asInstanceOf[Domain].typVars
          val types: Seq[Type] =
            Seq(DomainType(domainOfCalleePred, ListMap()), DomainType(domainOfCallerPred, ListMap()), Int)

          val mapNested: ListMap[TypeVar, Type] = ListMap(params.zip(types):_*)
          val assume = Inhale(DomainFuncApp(nestedFunc.get,
                                            Seq(varOfCalleePred, varOfCallerPred),
                                            mapNested)(calledPred.pos))(calledPred.pos)

          Seqn(Seq(assign1, assign2, assume), Nil)(calledPred.pos)
      }
      case c: CondExp =>
        val thn = rewritePredBodyAsExp(c.thn, origPred)
        val els = rewritePredBodyAsExp(c.els, origPred)
        If(c.cond, Seqn(Seq(thn), Nil)(c.pos), Seqn(Seq(els), Nil)(c.pos))(c.pos)
      case i: Implies =>
        val thn = rewritePredBodyAsExp(i.right, origPred)
        If(i.left, Seqn(Seq(thn), Nil)(i.pos), EmptyStmt)(i.pos)
      case b: BinExp =>
        val left = rewritePredBodyAsExp(b.left, origPred)
        val right = rewritePredBodyAsExp(b.right, origPred)
        Seqn(Seq(left, right), Nil)(b.pos)
      case u: UnExp => rewritePredBodyAsExp(u.exp, origPred)
      case _ => EmptyStmt
    }
  }

  /**
    * Rewrites given Expression (a,b,c,d,...) into one of the following form:
    * (a || (b && (c || (d && ... )))) or
    * (a && (b || (c && (d || ... ))))
    * @param decrArgs arguments which should be rewritten
    * @param conj     decides if the return expressions begins with a conjunction or a disjunction
    * @return the generated chain of con- and disjunctions
    */
  private def buildDecTree(decrArgs: Seq[Exp], conj: Boolean): Exp = {
    if (decrArgs.size == 1)
      decrArgs.head
    else if (conj)
      Or(decrArgs.head, buildDecTree(decrArgs.tail, conj = false))(decrArgs.head.pos)
    else
      And(decrArgs.head, buildDecTree(decrArgs.tail, conj = true))(decrArgs.head.pos)
  }

  /**
    * Does the same as 'buildDecTree(..)' but only with conjunctions
    * input a,b,c ==> a && b && c
    *
    * @param boundArgs arguments which should be used
    * @return the chain of conjunctions
    */
  private def buildBoundTree(boundArgs: Seq[Exp]): Exp = {
    if (boundArgs.size == 1)
      boundArgs.head
    else
      And(boundArgs.head, buildBoundTree(boundArgs.tail))(boundArgs.head.pos)
  }

  /**
    * Generates for a predicate and a variable the corresponding assignment
    * it generates the viper-representation of a predicate (via loc-domain and the proper domain-function)
    * and assign it to the given value
    *
    * @param pred        the predicate which defines the predicate-Domain and predicate-domainFunc
    * @param assLocation the variable, which should be assigned
    * @param argMap      an optional mapping used for replacing the arguments of the predicate
    * @return an assignment of the given variable to the representation of a predicate with the corresponding arguments
    */
  private def generateAssign(pred: PredicateAccessPredicate, assLocation: LocalVar, argMap: ListMap[Exp, Exp] = ListMap.empty)
                            : LocalVarAssign = {
    val domainOfPred: Domain = uniqueNameGen(pred.loc).asInstanceOf[Domain]
    val domainFunc = uniqueNameGen(pred).asInstanceOf[DomainFunc]
    val typVarMap: ListMap[TypeVar, Type] =
      ListMap(TypeVar(locationDomain.get.typVars.head.name) -> DomainType(domainOfPred, ListMap()))
    val assValue = DomainFuncApp(domainFunc, pred.loc.args.map(_.replace(argMap)), typVarMap)(pred.pos)
    LocalVarAssign(assLocation, assValue)(pred.pos)
  }

  /**
    * Replaces all functions (FuncApp) in an expression with their corresponding dummy-functions
    *
    * StrategyBuilder is used instead of replace,
    * due to the fact that the replace-method uses the Innermost-Traverse order, which stops after the first rewrite.
    * With the StrategyBuilder we can use the bottomUp-traverse-order which e.g. rewrites also function arguments.
    *
    * @param exp the expression which should be investigated
    * @return the same expression but with all functions replaced
    */
  private def replaceExpWithDummyFnc(exp: Exp): Exp =
    StrategyBuilder.Slim[Node]({ case fa: FuncApp => uniqueNameGen(fa) }, Traverse.BottomUp)
      .execute[Node](exp)
      .asInstanceOf[Exp]

  /**
    * Checks if a name already exists in the program and will add a counter to the name until the name is unique
    *
    * @param oldName name which should be checked
    * @return a name which is not already in the program
    */
  private def uniqueName(oldName: String): String = {
    var i = 1
    var newName = oldName
    while (members.contains(newName)) {
      newName = oldName + i
      i += 1
    }
    newName
  }

  /** Generator of the dummy-Functions, predicate-Domains and location-Functions
    * creates and stores the corresponding dumFunc, predDom or locFunc and returns it
    *
    * @param node function or predicate for which the corresponding structure should be generated
    * @return the needed dummy-function, pred-Domain or loc-Function
    */
  private def uniqueNameGen(node: Node): Node = {
    assert( node.isInstanceOf[Function] ||
            node.isInstanceOf[Predicate] ||
            node.isInstanceOf[FuncApp] ||
            node.isInstanceOf[PredicateAccess] ||
            node.isInstanceOf[PredicateAccessPredicate])

    node match {
      case f: Function =>
        if (neededDummyFncs.values.exists(_.name == f.name)) {
          neededPredDomains.values.find(_.name == f.name).get
        } else {
          if (neededDummyFncs.contains(f.name)) {
            neededDummyFncs(f.name)
          } else {
            val uniqueFuncName = uniqueName(f.name + "_withoutBody")
            val newFunc = Function(uniqueFuncName, f.formalArgs, f.typ, f.pres, Nil, None, None)(f.pos)
            members(uniqueFuncName) = newFunc
            neededDummyFncs(f.name) = newFunc
            newFunc
          }
        }
      case fa: FuncApp =>
        if (neededDummyFncs.values.exists(_.name == fa.funcname)) {
          FuncApp(neededDummyFncs.values.find(_.name == fa.funcname).get, fa.args)(fa.pos)
        } else {
          if (neededDummyFncs.contains(fa.funcname)) {
            FuncApp(neededDummyFncs(fa.funcname), fa.args)(fa.pos)
          } else {
            val uniqueFuncName = uniqueName(fa.funcname + "_withoutBody")
            val func = members(fa.funcname).asInstanceOf[Function]
            val newFunc = Function(uniqueFuncName, func.formalArgs, func.typ, func.pres, Nil, None, None)(func.pos)
            members(uniqueFuncName) = newFunc
            neededDummyFncs(fa.funcname) = newFunc
            FuncApp(newFunc, fa.args)(fa.pos)
          }
        }
      case p: PredicateAccess =>
        if (neededPredDomains.values.exists(_.name == p.predicateName)) {
          neededPredDomains.values.find(_.name == p.predicateName).get
        } else {
          if (neededPredDomains.contains(p.predicateName)) {
            neededPredDomains(p.predicateName)
          } else {
            val uniquePredName = uniqueName(p.predicateName + "_PredName")
            val newDomain = Domain(uniquePredName, Seq(), Seq(), Seq())(NoPosition)
            members(uniquePredName) = newDomain
            neededPredDomains(p.predicateName) = newDomain
            newDomain
          }
        }
      case pa: PredicateAccessPredicate =>
        if (neededLocFunctions.contains(pa.loc.predicateName)) {
          neededLocFunctions(pa.loc.predicateName)
        } else {
          val uniquePredFuncName =
            uniqueName("loc_" + pa.loc.args.map(_.typ).mkString("_").replaceAll("\\[", "").replaceAll("\\]", ""))
          val pred = members(pa.loc.predicateName).asInstanceOf[Predicate]
          val newLocFunc =
            DomainFunc(uniquePredFuncName,
                      pred.formalArgs,
                      DomainType(locationDomain.get,
                                ListMap(locationDomain.get.typVars.head -> locationDomain.get.typVars.head))
                      )(locationDomain.get.pos, locationDomain.get.info, locationDomain.get.name, locationDomain.get.errT)

          members(uniquePredFuncName) = newLocFunc
          neededLocFunctions(pa.loc.predicateName) = newLocFunc
          newLocFunc
        }
    }
  }

  /**
    * Generator of the predicate-variables, which represents the type 'predicate'
    *
    * @param p      predicate which defines the type of the variable
    * @param argMap optional replacement for the arguments
    * @return a local variable with the correct type
    */
  private def uniquePredLocVar(p: PredicateAccess, argMap: ListMap[Exp, Exp] = ListMap.empty): LocalVar = {
    val args = p.args map (_.replace(argMap))
    val predVarName = p.predicateName + "_" + args.hashCode().toString.replaceAll("-", "_")
    if (neededLocalVars.contains(p.predicateName)) {
      //Variable already exists
      neededLocalVars(p.predicateName).localVar
    } else {
      val info = SimpleInfo(Seq(p.predicateName + "_" + args.mkString(",")))
      val newLocalVar =
        LocalVar(predVarName)(DomainType(locationDomain.get,
                                        ListMap(TypeVar(locationDomain.get.typVars.head.name)
                                            -> DomainType(uniqueNameGen(p).asInstanceOf[Domain], ListMap()))),
                              info = info)
      neededLocalVars(predVarName) = LocalVarDecl(newLocalVar.name, newLocalVar.typ)(newLocalVar.pos, info)
      newLocalVar
    }
  }
}
