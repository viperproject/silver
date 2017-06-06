/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.verifier.errors.{AssertFailed, TerminationFailed}
import viper.silver.verifier.reasons.TerminationMeasure

//import viper.silver.verifier.errors.{AssertFailed, PreconditionInCallFalse, TerminationFailed}

import scala.collection.mutable

/** Utility methods for DecreaseClauses. */
  object DecreasesClause {

  //Delete decClause
  def rewriteForAll(funcs: Seq[Function]): Seq[Function] = {

    var functions = funcs map (deleteDec(_))
    functions
  }

  private def deleteDec(f: Function) = f match {
    case Function(_, _, _, _, _, decs, _) =>
      //f.decs = decs map dec
      f
  }

  //TODO
  // decreases x+y
  // multiple function calls -> multiple assertions
  def addMethod(funcs: Seq[Function], members: mutable.HashMap[String, Node]): Seq[Method] = {
    val methods = funcs map (addTerminationProof(_, members))
    methods
  }

  private def addTerminationProof(func: Function, members: mutable.HashMap[String, Node]): Method = {
    println("DecClauses: ")
    println(func.decs)
    var m = Method(func.name + "_termination_proof", func.formalArgs, Seq(), func.pres, func.posts, Seq(), Statements.EmptyStmt)(NoPosition, func.info, func.errT)
    m.body = stmt(func.body.get, members, func)
    m
  }

  def stmt(body: Exp, members: mutable.HashMap[String, Node], func: Function): Stmt = {

    body match {
      case CondExp(cond, thn, els) =>
        println("==CondExp")
        If(cond, stmt(thn, members, func), stmt(els, members, func))(body.pos)
      //case tr: PossibleTrigger =>

      //------------------------------
      //Other Triggers?
      case callee: FuncApp =>
        members.get("decreasing").get match {
          case df: DomainFunc =>

            val decClause = func.decs

            //Assume only one decreasesClause
            //TODO multiples decreasesClauses
            if (decClause.size == 1) {

              val callerArgs = func.formalArgs
              val calleeArgs = callee.getArgs

              val decreasingVarName = searchVarName(decClause.head)
              val indexOfDecVar = (decreasingVarName map (callerArgs.indexOf(_)))
              val usedCalleeArgs = calleeArgs.filter(e => indexOfDecVar.contains(calleeArgs.indexOf(e)))

              val rewriteExprMap = (decreasingVarName.map(_.name) zip usedCalleeArgs).toMap
              val smallerExpression = rewriteExpr(decClause.head, rewriteExprMap)
              val biggerExpression = decClause.head

              val pos = body.pos
              val info = SimpleInfo(Seq("TerminationCheck"))

              val errT = ErrTrafo({case AssertFailed(_, r) => TerminationFailed(callee, TerminationMeasure(decClause.head))})
              //val errT = ErrTrafo({case AssertFailed(_, r) => TerminationFailed(callee, r)})

              val paramTypes = (df.formalArgs map (_.typ))
              val argTypeVars = paramTypes.flatMap(p => p.typeVariables)

              //val argTypes = (callee.getArgs map (_.typ))
              //val map = (argTypeVars zip argTypes).toMap

              val map = Map(argTypeVars.head -> decClause.head.typ)

              Assert(DomainFuncApp(df, Seq(smallerExpression,biggerExpression), map)(df.pos))(pos, info, errT)

            } else { //Tuple
              println("Tuple - TODO")
              Statements.EmptyStmt
            }
        }
      case _ =>
        Statements.EmptyStmt
    }
  }

  def searchVarName(decClause: Exp): Seq[LocalVarDecl] = {
    decClause match {
      case a: AbstractLocalVar => Seq(LocalVarDecl(a.name, a.typ)(a.pos, a.info))
      case e: BinExp => searchVarName(e.left) ++ searchVarName(e.right)
      case e: UnExp => searchVarName(e.exp)
      case _ => Seq()
    }
  }

  def rewriteExpr(expr: Exp, newExpr: Map[String, Exp]): Exp = {
    expr match {
      case k: AbstractLocalVar =>
        newExpr(k.name)
      case binary: BinExp =>
        binary match {
          case e : Add => Add(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
          case e : Sub => Sub(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
          case e : Mul => Mul(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
          case e : Div => Div(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
          case e: Mod => Mod(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
        }
      case unary: UnExp =>
        unary match {
          case e: Minus => Minus(rewriteExpr(e.exp, newExpr))(unary.pos)
          //case PermMinus(exp) =>
        }
      case default => default
    }
  }
}