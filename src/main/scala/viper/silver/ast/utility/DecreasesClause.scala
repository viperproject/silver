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

import scala.collection.mutable

/** Utility methods for DecreaseClauses. */
object DecreasesClause {

  private var decreasingFunc: Option[DomainFunc] = None
  private var boundedFunc: Option[DomainFunc] = None
  private var nestedFunc: Option[DomainFunc] = None
  private var locationDomain: Option[Domain] = None

  private var neededLocalVars = collection.mutable.HashMap[String, LocalVarDecl]()
  private var neededDummyFncs = collection.mutable.HashMap[String, Function]()
  private var neededLocFunctions = collection.mutable.HashMap[String, DomainFunc]()
  private var neededPredDomains = collection.mutable.HashMap[String, Domain]()

  private var members = collection.mutable.HashMap[String, Node]()

  private def findFnc(name: String) = members(name).asInstanceOf[Function]


  /**
    * Adds to a given Program for every function a method, which can be used for verifying the termination of that function.
    * The methods will be constructed around a given decreases-Clause and will return corresponding error Messages
    *
    * @param funcs     all existing functions in a program
    * @param preds     all existing predicates in a program
    * @param doms      all existing domains in a program
    * @param decFunc   the decreasing Function. It takes two arguments and defines when a value is strictly "smaller"  than another.
    *                  It is used for proving decreasing values.
    * @param boundFunc the bounded Function. It takes one argument and defines if a value is bounded.
    * @param nestFunc  the nested Function. It takes two predicates as arguments, and defines when one predicate is "inside" another one
    * @param locDom    the location Domain. It is used to define a typ "Predicate", for showing decreasing predicates
    * @param members   a map from String to Node of all the currently existing structures in the Program
    * @return The necessary components (functions, methods, domains), which should be added in a viper program such that termination of functions can be verified
    */
  def addMethods(funcs: Seq[Function], preds: Seq[Predicate], doms: Seq[Domain], decFunc: Option[Node], boundFunc: Option[Node], nestFunc: Option[Node], locDom: Option[Node], members: mutable.HashMap[String, Node]): (Seq[Domain], Seq[Function], Seq[Method]) = {

    this.members = members

    neededDummyFncs = mutable.HashMap.empty
    neededLocFunctions = mutable.HashMap.empty
    neededPredDomains = mutable.HashMap.empty

    decreasingFunc = decFunc match {
      case Some(x) => Some(x.asInstanceOf[DomainFunc])
      case None => None
    }
    boundedFunc = boundFunc match {
      case Some(boundF) => Some(boundF.asInstanceOf[DomainFunc])
      case None => None
    }
    locationDomain = locDom match {
      case Some(locD) => Some(locD.asInstanceOf[Domain])
      case None => None
    }
    nestedFunc = nestFunc match {
      case Some(nestF) => Some(nestF.asInstanceOf[DomainFunc])
      case None => None
    }

    //Create for every Function a method which proofs the termination
    //Ignore funcions with 'decreases *' or with no body
    val methods = (funcs.filter(f => f.body.nonEmpty && (f.decs.isEmpty || !f.decs.get.isInstanceOf[DecStar])) map { func =>
      neededLocalVars = mutable.HashMap.empty
      val methodBody: Stmt = rewriteFuncBody(func.body.get, func, null, Set(), preds)

      val methodName = uniqueName(func.name + "_termination_proof")

      val newMethod = Method(methodName, func.formalArgs, Seq(), func.pres, Nil, Seqn(Seq(methodBody), neededLocalVars.values.toIndexedSeq)(methodBody.pos))(NoPosition, func.info, func.errT)
      members(methodName) = newMethod
      newMethod

    }).filter(_.body != EmptyStmt)

    if (neededLocFunctions.nonEmpty) {
      //There has to be functions in the location Domain. Therefore it deletes the 'old' location Domain and creates it again with now the needed domainfunctions
      assert(locationDomain.isDefined)
      val domainsWLoc = doms.filterNot(_ == locationDomain.get)
      val newLocDom = Domain(locationDomain.get.name, functions = neededLocFunctions.values.toSeq, locationDomain.get.axioms, locationDomain.get.typVars)(locationDomain.get.pos, locationDomain.get.info, locationDomain.get.errT)

      (domainsWLoc ++ Seq(newLocDom) ++ neededPredDomains.values.toSeq, neededDummyFncs.values.toSeq, methods)
    } else {
      (doms ++ neededPredDomains.values.toSeq, neededDummyFncs.values.toSeq, methods)
    }
  }

  /**
    * Transforms the body of a function into Statements, such that the termination of (direct or indirect) recursions can be verified.
    * The method stores needed domains, functions and local variables in global fields
    *
    * @param bodyToRewrite     Expression which will be transformed to statements
    * @param func              original Function
    * @param funcAppInOrigFunc is the position where the original function calls another Function. It is used for ErrorMeassges
    * @param alreadyChecked    set of functions which has been already traversed, to hinder infinity checks
    * @param predicates        set of all predicates, used in proof generation for decreasing predicates
    * @return a (sequence of) statement, which can be used for verifying termination of a given expression
    */
  private def rewriteFuncBody(bodyToRewrite: Exp, func: Function, funcAppInOrigFunc: FuncApp, alreadyChecked: Set[String], predicates: Seq[Predicate]): Stmt = {
    bodyToRewrite match {
      case pap: PredicateAccessPredicate =>
        //Add the assumption if the predicate has other predicate inside
        func.decs match {
          case Some(DecTuple(_)) =>
            val pred: Predicate = predicates.find(_.name == pap.loc.predicateName).get

            pred.body match {
              case Some(body) =>
                if (locationDomain.isDefined && nestedFunc.isDefined) {
                  //Cast arguments from type LocalVarDecl to LocalVar
                  val formalArgs = pred.formalArgs map {
                    varDecl => LocalVar(varDecl.name)(varDecl.typ, varDecl.pos, varDecl.info, varDecl.errT)
                  }
                  //Generate nested-assumption
                  rewritePredBodyAsExp(body.replace((formalArgs zip pap.loc.args).toMap), pap)
                } else {
                  if (locationDomain.isEmpty) {
                    Consistency.messages ++= FastMessaging.message(func, "missing location-Domain (for assuming nested predicates)")
                  }
                  if (nestedFunc.isEmpty) {
                    Consistency.messages ++= FastMessaging.message(func, "missing nested-Relation (for assuming nested predicates)")
                  }
                  EmptyStmt
                }
              //Predicate has no body
              case None => EmptyStmt
            }
          //No decreasing Clause
          case _ => EmptyStmt
        }

      case CondExp(cond, thn, els) =>
        //Check for possible recursion inside of the condition
        val termCheckInCond = rewriteFuncBody(cond, func, funcAppInOrigFunc, alreadyChecked, predicates)
        val thnSt = rewriteFuncBody(thn, func, funcAppInOrigFunc, alreadyChecked, predicates)
        val elsSt = rewriteFuncBody(els, func, funcAppInOrigFunc, alreadyChecked, predicates)

        val wholeCond = if (thnSt == EmptyStmt && elsSt == EmptyStmt) EmptyStmt else {
          If(replaceExpWithDummyFnc(cond), Seqn(Seq(thnSt), Nil)(bodyToRewrite.pos), Seqn(Seq(elsSt), Nil)(bodyToRewrite.pos))(bodyToRewrite.pos)
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
          //Called Function is not the original function => no recursion so far
          if (!alreadyChecked.contains(callee.funcname)) {
            //Program didnt check this function for recursion yet
            val calledFunc = findFnc(callee.funcname)

            calledFunc.decs match {
              case Some(DecStar()) =>
                //The called Function might not terminate
                val functionInOrigBody = if (funcAppInOrigFunc == null) callee else funcAppInOrigFunc

                val errTr = ErrTrafo({ case AssertFailed(_, _, _) => TerminationFailed(func, CallingNonTerminatingFunction(functionInOrigBody, calledFunc)) })
                val info = SimpleInfo(Seq("Called Fnc (" + callee.funcname + ") does not terminate"))
                Seqn(termChecksOfArgs ++ Seq(Assert(FalseLit()(func.pos))(pos = func.pos, info, errT = errTr)), Nil)(bodyToRewrite.pos)

              case _ =>
                //Check the called Function for recursion

                //Cast arguments from type LocalVarDecl to LocalVar
                val formalArgsOfCallee = calledFunc.formalArgs map {
                  varDecl => LocalVar(varDecl.name)(varDecl.typ, varDecl.pos, varDecl.info, varDecl.errT)
                }

                //Arguments are now checked -> to not check same recursions again, replace them with their dummyFnc
                val mapFormalArgsToCalledArgs = (formalArgsOfCallee zip (calleeArgs map replaceExpWithDummyFnc)).toMap

                if (calledFunc.body.nonEmpty) {
                  val body = calledFunc.body.get.replace(mapFormalArgsToCalledArgs)

                  //Check for recursion in the new function-body
                  val termCheckOfFuncBody = rewriteFuncBody(body, func, if (funcAppInOrigFunc == null) callee else funcAppInOrigFunc, alreadyChecked ++ Set(callee.funcname), predicates) //canReturn = false,

                  //Replace 'result' in the postconditions with the function and the correct arguments
                  val resultNodes = calledFunc.posts flatMap (p => p.deepCollect { case r: Result => r })
                  val postConds: Seq[Exp] = calledFunc.posts map (p =>
                    p.replace(mapFormalArgsToCalledArgs).replace((resultNodes zip List.fill(resultNodes.size)(FuncApp(calledFunc, calleeArgs)(body.pos))).toMap))

                  val inhalePostConds = postConds map (c => Inhale(replaceExpWithDummyFnc(c))(body.pos))

                  val inhaleFuncBody = Inhale(replaceExpWithDummyFnc(EqCmp(FuncApp(calledFunc, calleeArgs)(body.pos), body)(body.pos)))(body.pos)
                  Seqn(termChecksOfArgs ++ Seq(termCheckOfFuncBody, inhaleFuncBody) ++ inhalePostConds, Nil)(body.pos)
                } else {
                  //Function has no body

                  //Replace 'result' in the postconditions with the function and the correct arguments
                  val resultNodes = calledFunc.posts flatMap (p => p.deepCollect { case r: Result => r })
                  val postConds: Seq[Exp] = calledFunc.posts map (p =>
                    p.replace(mapFormalArgsToCalledArgs).replace((resultNodes zip List.fill(resultNodes.size)(FuncApp(calledFunc, calleeArgs)(bodyToRewrite.pos))).toMap))

                  val inhalePostConds = postConds map (c => Inhale(replaceExpWithDummyFnc(c))(bodyToRewrite.pos))
                  Seqn(termChecksOfArgs ++ inhalePostConds, Nil)(bodyToRewrite.pos)
                }
            }
          } else {
            //Program already checked this function for recursion
            Seqn(termChecksOfArgs, Nil)(bodyToRewrite.pos)
          }
        } else {
          //Called Function is the same as the original one => recursion detected
          if (decrClauseOfOrigFnc.isEmpty) {
            //There is no decrease Clause
            //Give an error, because there is a recursion but no decreases clause

            val functionInOrigBody = if (funcAppInOrigFunc == null) callee else funcAppInOrigFunc
            val errTr = ErrTrafo({ case AssertFailed(_, _, _) => TerminationFailed(func, NoDecClauseSpecified(functionInOrigBody)) })
            Assert(FalseLit()(func.pos))(pos = func.pos, info = SimpleInfo(Seq("Recursion but no decClause")), errT = errTr)

          } else {
            //Decrease Clause is defined
            assert(!decrClauseOfOrigFnc.get.isInstanceOf[DecStar])
            //Replace in the decreaseClause every argument with the correct call
            decrClauseOfOrigFnc match {

              case Some(DecTuple(decreasingExp)) =>
                if (decreasingFunc.isDefined && boundedFunc.isDefined && (decreasingExp.collect { case p: PredicateAccessPredicate => p }.isEmpty || locationDomain.isDefined)) {

                  //Cast Arguments to LocalVariables(Exp)1
                  val formalArgs: Seq[LocalVar] = func.formalArgs map {
                    varDecl => LocalVar(varDecl.name)(varDecl.typ, varDecl.pos, varDecl.info, varDecl.errT)
                  }

                  var neededArgAssigns: Seq[Stmt] = Nil //Needed for decreasing predicates

                  var varDecls: Seq[Declaration] = Nil
                  //decreasing(smallerExpr, biggerExpr) <==> smallerExpr '<<' biggerExpr
                  val smallerExpression: Seq[Exp] = decreasingExp map {
                    case pap: PredicateAccessPredicate =>

                      val varOfCalleePred = uniquePredLocVar(pap.loc, (formalArgs zip calleeArgs).toMap)

                      varDecls :+= LocalVarDecl(varOfCalleePred.name, varOfCalleePred.typ)(varOfCalleePred.pos, varOfCalleePred.info)
                      neededArgAssigns :+= generateAssign(pap, varOfCalleePred, (formalArgs zip calleeArgs).toMap)
                      varOfCalleePred
                    case decC => decC.replace((formalArgs zip calleeArgs).toMap)
                  }

                  val biggerExpression: Seq[Exp] = decreasingExp map {
                    case pap: PredicateAccessPredicate =>
                      assert(locationDomain.isDefined)
                      val varOfCalleePred = uniquePredLocVar(pap.loc)
                      varDecls :+= LocalVarDecl(varOfCalleePred.name, varOfCalleePred.typ)(varOfCalleePred.pos, varOfCalleePred.info)
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

                  //Map AssertionErrors to TerminationFailedErrors with noBound - Reason
                  val errTBound = ErrTrafo({ case AssertFailed(_, reason, _) => TerminationFailed(func, reason match {
                    case AssertionFalse(offendingNode) => offendingNode match {
                      //offendingNode of the Assertion-reason is "bounded(...): DomainFuncApp"
                      case dfa: DomainFuncApp =>
                        assert(dfa.args.size == 1)
                        TerminationNoBound(DecTuple(decreasingExp)(callerFunctionInOrigBody.pos), dfa.args.head match {
                          case PredicateAccessPredicate(loc, _) => loc //Per default predicates are always bounded -> only used when user rewrites bounded(p: Predicate)
                          case d => d
                        })
                      case _ => reason
                    }
                  })
                  })

                  //Map AssertionErrors to TerminationFailedErrors with noBound - Reason
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

                  //Generation of termination Checks - (Assert decreasing(..,..))
                  //Generates (for a decreasing Clause: 'decreases a,b,c') a sequence with the following form: (dec(a,a), a==a, dec(b,b), b==b, dec(c,c))
                  for (i <- argsForTermProof.indices) {
                    if (i > 0) {
                      decrFunc :+= EqCmp(argsForTermProof(i - 1)._1, argsForTermProof(i - 1)._2)(decreasingFunc.get.pos)
                    }
                    decrFunc :+= replaceExpWithDummyFnc(DomainFuncApp(decreasingFunc.get, Seq(argsForTermProof(i)._1, argsForTermProof(i)._2), Map(argTypeVarsDecr.head -> argsForTermProof(i)._1.typ, argTypeVarsDecr.last -> argsForTermProof(i)._2.typ))(callerFunctionInOrigBody.pos))
                    boundFunc :+= replaceExpWithDummyFnc(DomainFuncApp(boundedFunc.get, Seq(argsForTermProof(i)._2), Map(argTypeVarsDecr.head -> argsForTermProof(i)._2.typ))(callerFunctionInOrigBody.pos))
                  }

                  //Generate from the Seq the correct Assertions
                  val boundedAss = Assert(buildBoundTree(boundFunc))(callerFunctionInOrigBody.pos, infoBound, errTBound)
                  val decreaseAss = Assert(buildDecTree(decrFunc, conj = true))(callerFunctionInOrigBody.pos, infoDecr, errTDecr)

                  if (funcAppInOrigFunc == null) { //we are in the first called function

                    val bodyWithArgs = func.body.get.replace((formalArgs zip calleeArgs).toMap)

                    //Replace 'result' in the postconditions with the dummy-Function and the correct arguments
                    val resultNodes = func.posts flatMap (p => p.deepCollect { case r: Result => r })
                    val postConds = func.posts map (p =>
                      p.replace((formalArgs zip calleeArgs).toMap).replace((resultNodes zip List.fill(resultNodes.size)(FuncApp(func, calleeArgs)(pos))).toMap))
                    val inhalePostConds = postConds map (c => Inhale(replaceExpWithDummyFnc(c))(pos))

                    val inhaleFuncBody = Inhale(replaceExpWithDummyFnc(EqCmp(FuncApp(func, calleeArgs)(pos), bodyWithArgs)(pos)))(pos)
                    //varDecls
                    Seqn(termChecksOfArgs ++ neededArgAssigns ++ Seq(boundedAss, decreaseAss, inhaleFuncBody) ++ inhalePostConds, Nil)(pos)
                  } else {
                    Seqn(termChecksOfArgs ++ neededArgAssigns ++ Seq(boundedAss, decreaseAss), Nil)(pos)
                  }
                } else {
                  if (decreasingFunc.isEmpty) {
                    Consistency.messages ++= FastMessaging.message(func, "missing decreasing-Function")
                  }
                  if (boundedFunc.isEmpty) {
                    Consistency.messages ++= FastMessaging.message(func, "missing bounded-Function")
                  }
                  if (decreasingExp.collect { case p: PredicateAccessPredicate => p }.nonEmpty && locationDomain.isEmpty) {
                    Consistency.messages ++= FastMessaging.message(func, "missing location-Domain (needed for proving termination over predicates)")
                  }
                  EmptyStmt
                }
            }
          }
        }

      case b: BinExp =>
        val left = rewriteFuncBody(b.left, func, funcAppInOrigFunc, alreadyChecked, predicates)
        val right = rewriteFuncBody(b.right, func, funcAppInOrigFunc, alreadyChecked, predicates)
        //Short circuit evaluation
        b match {
          case _: Or =>
            Seqn(Seq(left, If(Not(replaceExpWithDummyFnc(b.left))(b.pos), Seqn(Seq(right), Nil)(b.pos), EmptyStmt)(b.pos)), Nil)(b.pos)
          case _: And =>
            Seqn(Seq(left, If(replaceExpWithDummyFnc(b.left), Seqn(Seq(right), Nil)(b.pos), EmptyStmt)(b.pos)), Nil)(b.pos)
          case _: Implies =>
            Seqn(Seq(left, If(replaceExpWithDummyFnc(b.left), Seqn(Seq(right), Nil)(b.pos), EmptyStmt)(b.pos)), Nil)(b.pos)
          case _ =>
            Seqn(Seq(left, right), Nil)(b.pos)
        }
      case u: UnExp => rewriteFuncBody(u.exp, func, funcAppInOrigFunc, alreadyChecked, predicates)
      case _: Exp => EmptyStmt
    }
  }

  /**
    * Traverses a predicate body and adds corresponding inhales of the 'nested'-Relation iff a predicate is inside of this body
    *
    * @param body     The part of the predicate-body which should be analyzed
    * @param origPred The body of the original predicate which should be analyzed
    * @return Statements with the generated inhales (Inhale(nested(pred1, pred2)))
    */
  private def rewritePredBodyAsExp(body: Exp, origPred: PredicateAccessPredicate): (Stmt) = {

    body match {
      case ap: AccessPredicate => ap match {
        case FieldAccessPredicate(_, _) => EmptyStmt
        case calledPred: PredicateAccessPredicate =>
          assert(locationDomain.isDefined)
          assert(nestedFunc.isDefined)

          //Predicate-Domains (p_PredName)
          val domainOfCallerPred: Domain = uniqueNameGen(origPred.loc).asInstanceOf[Domain]
          val domainOfCalleePred: Domain = uniqueNameGen(calledPred.loc).asInstanceOf[Domain]

          //Local variables
          val varOfCallerPred: LocalVar = uniquePredLocVar(origPred.loc)
          val declCaller = LocalVarDecl(varOfCallerPred.name, varOfCallerPred.typ)(varOfCallerPred.pos, varOfCallerPred.info)
          val varOfCalleePred: LocalVar = uniquePredLocVar(calledPred.loc)
          val declCallee = LocalVarDecl(varOfCalleePred.name, varOfCalleePred.typ)(varOfCalleePred.pos, varOfCalleePred.info)

          //Assign
          val assign1 = generateAssign(origPred, varOfCallerPred)
          val assign2 = generateAssign(calledPred, varOfCalleePred)

          //Inhale nested-Relation
          val mapNested: Map[TypeVar, Type] = Map(TypeVar("N1") -> DomainType(domainOfCalleePred, Map()), TypeVar("N2") -> DomainType(domainOfCallerPred, Map()))
          val assume = Inhale(DomainFuncApp(nestedFunc.get, Seq(varOfCalleePred, varOfCallerPred), mapNested)(calledPred.pos))(calledPred.pos)

          //Seq(declCaller, declCallee)
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
    * Rewrites given Expression (a,b,c,d,...) into the following form:
    * (a || (b && (c || d)))
    *
    * @param decrArgs aruments which should be rewritten
    * @param conj     decides if the return expressions begins with a conjuction of a disjuntion
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
    * Does the same as 'buildDecTree(..)' but only with conjuctions
    * Input a,b,c ==> a && b && c
    *
    * @param boundArgs arguments which should be used
    * @return the chain of conjuctions
    */
  private def buildBoundTree(boundArgs: Seq[Exp]): Exp = {
    if (boundArgs.size == 1)
      boundArgs.head
    else
      And(boundArgs.head, buildBoundTree(boundArgs.tail))(boundArgs.head.pos)
  }

  /**
    * Generates for a predicate and a variable the corresponding Assignment.
    * It generates the viper-representation of a predicate (via Loc-domain and the proper domain-function) and assign it to the given value
    *
    * @param pred        the Predicate which defines the predicate-Domain and predicate-domainFunc
    * @param assLocation the variable, which should be assigned
    * @param argMap      an optional mapping used for replacing the arguments of the predicate
    * @return an Assignment of the given variable to the representation of a predicate with the corresponding arguments
    */
  private def generateAssign(pred: PredicateAccessPredicate, assLocation: LocalVar, argMap: Map[Exp, Exp] = Map()): LocalVarAssign = {
    val domainOfPred: Domain = uniqueNameGen(pred.loc).asInstanceOf[Domain]
    val domainFunc = uniqueNameGen(pred).asInstanceOf[DomainFunc]
    val typVarMap: Map[TypeVar, Type] = Map(TypeVar(locationDomain.get.typVars.head.name) -> DomainType(domainOfPred, Map()))
    val assValue = DomainFuncApp(domainFunc, pred.loc.args.map(_.replace(argMap)), typVarMap)(pred.pos)
    LocalVarAssign(assLocation, assValue)(pred.pos)
  }

  /**
    * Replaces all functions (FuncApp) in a expression with their corresponding dummy-functions
    *
    * StrategyBuilder is used instead of replace, due to the fact that the replace-method uses the Innermost-Traverse order, which stops after the first rewrite.
    * With the StrategyBuilder we can use the bottomUp-traverse-order which e.g. rewrites also function arguments
    *
    * @param exp the expression which should be investigated
    * @return the same expreassion but with all functions replaced
    */
  private def replaceExpWithDummyFnc(exp: Exp): Exp = StrategyBuilder.Slim[Node]({ case fa: FuncApp => uniqueNameGen(fa) }, Traverse.BottomUp).execute[Node](exp).asInstanceOf[Exp]

  /**
    * Checks if a name already is existence in the program and adds a counter to the name until the name is unique
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
    *
    * @param node function or predicate for which the corresponding structure should be generated
    * @return the needed dummy-funtion, pred-Domain or loc-Function
    */
  private def uniqueNameGen(node: Node): Node = {
    assert(node.isInstanceOf[Function] || node.isInstanceOf[Predicate] || node.isInstanceOf[FuncApp] || node.isInstanceOf[PredicateAccess] || node.isInstanceOf[PredicateAccessPredicate])

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
          val uniquePredFuncName = uniqueName("loc_" + pa.loc.args.map(_.typ).mkString("_").replaceAll("\\[", "").replaceAll("\\]", ""))
          val pred = members(pa.loc.predicateName).asInstanceOf[Predicate]
          val newLocFunc = DomainFunc(uniquePredFuncName, pred.formalArgs, DomainType(locationDomain.get, Map(locationDomain.get.typVars.head -> locationDomain.get.typVars.head)))(locationDomain.get.pos, locationDomain.get.info, locationDomain.get.name, locationDomain.get.errT)

          members(uniquePredFuncName) = newLocFunc
          neededLocFunctions(pa.loc.predicateName) = newLocFunc
          newLocFunc
        }
    }
  }

  /**
    * Generator of the predicate-variables with the correct type
    *
    * @param p      predicate which defines the type of the variable
    * @param argMap optional replacement for the arguments
    * @return a local Variable with the correct type
    */
  private def uniquePredLocVar(p: PredicateAccess, argMap: Map[Exp, Exp] = Map()): LocalVar = {
    val args = p.args map (_.replace(argMap))
    val predVarName = p.predicateName + "_" + args.hashCode().toString.replaceAll("-", "_")
//    var predVarName = p.predicateName + "_" + counter
    if (neededLocalVars.contains(p.predicateName)) {
      //Variable already exists
      neededLocalVars(p.predicateName).localVar
    } else {
      val info = SimpleInfo(Seq(p.predicateName + "_" + args.mkString(",")))
      val newLocalVar = LocalVar(predVarName)(DomainType(locationDomain.get, Map(TypeVar(locationDomain.get.typVars.head.name) -> DomainType(uniqueNameGen(p).asInstanceOf[Domain], Map()))), info = info)
      neededLocalVars(predVarName) = LocalVarDecl(newLocalVar.name, newLocalVar.typ)(newLocalVar.pos, info)
      newLocalVar
    }
  }
}