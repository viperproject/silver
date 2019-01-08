package viper.silver.plugin

import viper.silver.ast.{CondExp, DecStar, DecTuple, Exp, FuncApp, Function, If, Method, Program, Seqn, Stmt}
import viper.silver.ast.utility.Functions
import viper.silver.ast.utility.Statements.EmptyStmt

class SimpleDecreasePlugin extends SilverPlugin
{
  /*
  /** Called after methods are filtered but before the verification by the backend happens.
    *
    * @param input AST
    * @return Modified AST
    */
  override def beforeVerify(input: Program): Program = {

    ProgramTransformation.transformProgram(input)
  }
}

object ProgramTransformation{


  def transformProgram(program: Program): Program ={
    val callGraph = Functions.getFunctionCallgraph(program)
    val heights = Functions.heights(program)

    val functions = callGraph.vertexSet()

    functions.forEach(function => {
      if (function.decs.isDefined && !function.decs.get.isInstanceOf[DecStar]) {
        val edges = callGraph.edgesOf(function)

        // TODO: create proof Method for function
        rewriteFunction(function.body.get, function, heights)
        // for each function call check if they have the same height
        // If yes add termination checks

        edges.forEach(edge => {
          val target = callGraph.getEdgeTarget(edge)

          if (target.decs.isDefined && target.decs.get.isInstanceOf[DecStar]) {

          }else if (target.decs.isDefined){

            if (heights(function) == heights(target)) {
              // same cluster both
              val originDec = function.decs.asInstanceOf[DecTuple]
              val targetDec = target.decs.asInstanceOf[DecTuple]
              // all expressions of both functions with same type
              val exps = originDec.exp.zip(targetDec.exp).takeWhile {case (l, r) => l.isSubtype(r) && r.isSubtype(l)}


            }
          }else{
            // termination measure not defined in target

          }
        })
      }
    })

    program
  }

  private def rewriteFunction(body: Exp, start: Function, heights: Map[Function, Int]): Stmt = {
    body match {
      case callee: FuncApp =>
        if(heights(start) == heights(callee)){

        }else{
          // not in the same cluster
          EmptyStmt
        }
      case CondExp(cond, thn, els) =>
        val termCheckInCond = rewriteFunction(cond, start, heights)
        val thenSt = rewriteFunction(thn, start, heights)
        val elseSt = rewriteFunction(els, start, heights)

        val wholeCond: Stmt = if (thenSt == EmptyStmt && elseSt == EmptyStmt) {
          EmptyStmt
        } else {
          If(cond, Seqn(Seq(thenSt), Nil)(body.pos), Seqn(Seq(elseSt), Nil)(body.pos))(body.pos)
        }
        Seqn(Seq(termCheckInCond, wholeCond), Nil)(body.pos)
    }
  }

  private def getTerminationCheck(caller: Function, callee: Function): Stmt = {
    if (caller.decs.isEmpty){
      EmptyStmt
    }else if(caller.decs.get.isInstanceOf[DecStar]){
      EmptyStmt
    } else if(callee.decs.isEmpty){
      EmptyStmt
    } else if(callee.decs.get.isInstanceOf[DecStar]){
      EmptyStmt
    }else{
      // both have a decrease clause
      val callerDec = caller.decs.get.asInstanceOf[DecTuple]
      val calleeDec = callee.decs.get.asInstanceOf[DecTuple]

      // all expressions of both functions with same type
      val exps = callerDec.exp.zip(calleeDec.exp).takeWhile {case (l, r) => l.isSubtype(r) && r.isSubtype(l)}

      // TODO introduce parameters of callee as new variables and assign them the arguments from caller

      // TODO put all the checks together into an assert

    }

  }
  */
}
