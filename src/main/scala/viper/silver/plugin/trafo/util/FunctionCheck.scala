// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.trafo.util

import viper.silver.ast.utility.{Functions, ViperStrategy}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{ErrTrafo, Exp, FuncApp, Function, Inhale, LocalVar, LocalVarDecl, Method, NodeTrafo, Program, Result, Seqn, Stmt}
import viper.silver.verifier.errors.AssertFailed
import viper.silver.plugin.{DecreasesExp, DecreasesStar, DecreasesTuple}

import scala.collection.immutable.ListMap

trait FunctionCheck extends ProgramManager with DecreasesCheck with ExpTransformer {

  private val heights: Map[Function, Int] = Functions.heights(program)
  private def compareHeights(f1: Function, f2: Function): Boolean = {
    // assuming heights (as computed by Function.heights(program))are always non-negative
    heights.getOrElse(f1, -1) == heights.getOrElse(f2, -2)
  }

  /**
    * This function should be used to access all the DecreasesExp
    * @param function for which the decreases exp is defined
    * @return the defined DecreasesExp or a DecreasesTuple with the parameters as the arguments
    */
  def getFunctionDecreasesExp(function: Function): DecreasesExp = {
    functionsDec.getOrElse(function, {
      DecreasesTuple(function.formalArgs.map(_.localVar))(pos = function.pos, errT = NodeTrafo(function))
    })
  }
  val functionsDec: Map[Function, DecreasesExp]

  protected override def generateCheckProgram(): Program = {
    program.functions.filterNot(f => f.body.isEmpty || getFunctionDecreasesExp(f).isInstanceOf[DecreasesStar]).foreach(f => {
      // method proving termination of the functions body.
      val checkMethodNameBody = uniqueName(f.name + "_termination_proof")
      val contextBody = FContext(f, checkMethodNameBody)

      val checkBody = transformExp(f.body.get, contextBody)

      // get all predicate init values which are used.
      val newVarBody = getMethodsInitPredicateInstanceVar(checkMethodNameBody)
      val newVarAssBody: Seq[Stmt] = newVarBody.map(v => generatePredicateAssign(v._2.localVar, v._1.loc)).toSeq

      val checkMethodBody = Method(checkMethodNameBody, f.formalArgs, Nil, f.pres, Nil,
                              Option(Seqn(newVarAssBody :+ checkBody, newVarBody.values.toIndexedSeq)()))()

      methods(checkMethodNameBody) = checkMethodBody


      // method proving termination of postconditions.
      val checkMethodNamePosts = uniqueName(f.name + "_posts_termination_proof")
      val contextPosts = FContext(f, checkMethodNamePosts)
      val resultVariableName = "$result"
      val resultVariable = LocalVarDecl(resultVariableName, f.typ)(f.result.pos, f.result.info, NodeTrafo(f.result))

      // replace all Result nodes with the result variable.
      val posts = f.posts.map(p => ViperStrategy.Slim({
        case r@Result() => LocalVar(resultVariableName)(r.typ, r.pos, r.info, NodeTrafo(r))
      }, Traverse.BottomUp).execute[Exp](p))

      // after the termination checks assume the postcondition.
      val checkPosts = posts.map(p => {
        Seqn(Seq(transformExp(p, contextPosts), Inhale(p)(p.pos, p.info, p.errT)), Nil)()
      })

      // get all predicate init values which are used.
      val newVarPosts = getMethodsInitPredicateInstanceVar(checkMethodNamePosts)
      val newVarAssPosts: Seq[Stmt] = newVarPosts.map(v => generatePredicateAssign(v._2.localVar, v._1.loc)).toSeq

      val checkMethodPosts = Method(checkMethodNamePosts, f.formalArgs, Seq(resultVariable), f.pres, Nil,
                          Option(Seqn(newVarAssPosts ++ checkPosts, newVarPosts.values.toIndexedSeq)()))()

      methods(checkMethodNamePosts) = checkMethodPosts
    })

    super.generateCheckProgram()
  }


  /**
    * Adds case FuncApp
    * Checks if the termination measure decreases in every function call (to a possibly
    * recursive call)
    *
    * @return a statement representing the expression
    */
  override def transformExp: PartialFunction[(Exp, Context), Stmt] = {
    case (callee: FuncApp, context: Context) =>
      assert(context.isInstanceOf[FunctionContext], "Wrong context used for transformFuncBody")
      val func = context.asInstanceOf[FunctionContext].func

      val stmts = collection.mutable.ArrayBuffer[Stmt]()

      // check the arguments
      val termChecksOfArgs: Seq[Stmt] = callee.getArgs map (a => transformExp(a, context))
      stmts.appendAll(termChecksOfArgs)

      val calledFunc = functions(callee.funcname)
      val calleeArgs = callee.getArgs

      if (compareHeights(func, calledFunc)) {
        // In the same cycle. => compare

        // map of parameters in the called function to parameters in the current functions (for substitution)
        val mapFormalArgsToCalledArgs = ListMap(calledFunc.formalArgs.map(_.localVar).zip(calleeArgs): _*)

        val decOrigin = getFunctionDecreasesExp(func)
        val decDest = getFunctionDecreasesExp(calledFunc)

        assert(decOrigin.isInstanceOf[DecreasesTuple], "Checking a function with DecreasesStar for termination! " +
          "This should not happen!")

        val errTrafo = ErrTrafo({
          case AssertFailed(_, r, c) => FunctionTerminationError(callee, r, c)
          case d => d
        })

        val reasonTrafoFactory = SimpleReasonTrafoFactory(decOrigin.asInstanceOf[DecreasesTuple])

        val terminationCheck = createTerminationCheck(decOrigin, decDest, mapFormalArgsToCalledArgs, errTrafo, reasonTrafoFactory, context.asInstanceOf[ProofMethodContext])

        val assertion = terminationCheck

        stmts.appendAll(Seq(assertion))
      } else {
        // not in the same cycle
      }
      Seqn(stmts, Nil)()
    case default => super.transformExp(default)
  }
  case class FContext(override val func: Function, override val methodName: String) extends FunctionContext

}

trait FunctionContext extends Context with ProofMethodContext {
  val func: Function
}

