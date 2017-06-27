/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.verifier.errors.{AssertFailed, TerminationFailed}
import viper.silver.verifier.reasons.{AssertionFalse, TerminationMeasure, TerminationNoBound}

import scala.collection.mutable

/** Utility methods for DecreaseClauses. */
object DecreasesClause {

  //TODO
  // multiple function calls -> multiple assertions
  def addMethod(funcs: Seq[Function], decreasingFunc : DomainFunc, boundedFunc : DomainFunc, findFnc : (String) => Function): Seq[Method] = {
    val methods = funcs map (addTerminationProof(_, decreasingFunc, boundedFunc, findFnc))
    methods
  }

  private def addTerminationProof(func: Function, decreasingFunc: DomainFunc, boundedFunc: DomainFunc, findFnc: (String) => Function): Method = {
    println("DecClauses: ")
    println(func.decs)
    val m = Method(func.name + "_termination_proof", func.formalArgs, Seq(), func.pres, func.posts, Seq(), Statements.EmptyStmt)(NoPosition, func.info, func.errT)

    m.body = rewriteExpAsStmts(func.body.get, decreasingFunc, boundedFunc, func, Set(), findFnc)
    m
  }

  def rewriteExpAsStmts(body: Exp, decreasingFunc: DomainFunc, boundedFunc: DomainFunc, func: Function, alreadyChecked: Set[String], findFnc: (String) => Function): Stmt = {

    //Replace all the variables with the called Arguments (Used especially i mutual recursion)
    //TODO replace is only right after a function call -> do it there directly
    //val body = b.replace(callerArgs)

    //TODO replace
    body match {
      case _: AccessPredicate => Statements.EmptyStmt
      case InhaleExhaleExp(in, ex) => Statements.EmptyStmt
      case _: PermExp => Statements.EmptyStmt
      case _: LocationAccess => Statements.EmptyStmt
      case CondExp(cond, thn, els) =>
        val s1 = rewriteExpAsStmts(cond, decreasingFunc, boundedFunc, func, alreadyChecked, findFnc)
        val s2 = If(cond, rewriteExpAsStmts(thn, decreasingFunc, boundedFunc, func, alreadyChecked, findFnc), rewriteExpAsStmts(els, decreasingFunc, boundedFunc, func, alreadyChecked, findFnc))(body.pos)
        Seqn(Seq(s1, s2))(body.pos)
      case Unfolding(acc, unfBody) =>
        val s1 = Unfold(acc)(unfBody.pos)
        val s2 = rewriteExpAsStmts(unfBody, decreasingFunc, boundedFunc, func, alreadyChecked, findFnc)
        val s3 = Fold(acc)(unfBody.pos)
        Seqn(Seq(s1, s2, s3))(unfBody.pos)
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

        var decClause = func.decs

        //If no decreasing argument is given, try to proof termination by decreasing the first argument
        if(decClause.isEmpty){
          decClause = Seq(LocalVar(func.formalArgs.head.name)(func.formalArgs.head.typ))
        }

        val calleeArgs = callee.getArgs
        val termCheckOfArgs = calleeArgs map (rewriteExpAsStmts(_, decreasingFunc, boundedFunc, func, alreadyChecked, findFnc))



        //Assume only one decreasesClause
        //TODO multiples decreasesClauses
        if (decClause.nonEmpty) { //There is a decrease Clause //TODO no decClause size=0

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

              val newFormalArgs = callee.formalArgs map {
                case l: LocalVarDecl => LocalVar(l.name)(l.typ) //, l.pos, l.info, l.errT)
                case a => a
              }

              var body = newFunc.body.get
              //body = body.replace((newFormalArgs.asInstanceOf[Seq[Exp]] zip calleeArgs).toMap)
              body = body.replace((newFormalArgs zip calleeArgs).toMap)


              val termCheckOfFuncBody = rewriteExpAsStmts(body, decreasingFunc, boundedFunc, func, alreadyChecked ++ Set(callee.funcname), findFnc)
              Seqn(termCheckOfArgs ++ Seq(termCheckOfFuncBody))(body.pos)
            } else {
              Seqn(termCheckOfArgs)(body.pos)
            }

          //Called Function is the same as the original one => recursion detected
          } else {

            val formalArgs = func.formalArgs map {
              case l: LocalVarDecl => LocalVar(l.name)(l.typ) //, l.pos, l.info, l.errT)
              case a => a
            }

            //Replace in the decreaseClause every argument with the correct call
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
          }
        } else { //No DecClause
          println("TODO") //TODO should not be called at all / dont create additional method
          Seqn(termCheckOfArgs)(body.pos)
        }

      case b: BinExp => Seqn(Seq(rewriteExpAsStmts(b.left, decreasingFunc, boundedFunc, func, alreadyChecked, findFnc), rewriteExpAsStmts(b.right, decreasingFunc, boundedFunc, func, alreadyChecked, findFnc)))(body.pos)
      case u: UnExp => rewriteExpAsStmts(u.exp, decreasingFunc, boundedFunc, func, alreadyChecked, findFnc)
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