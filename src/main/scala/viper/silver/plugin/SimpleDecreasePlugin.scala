package viper.silver.plugin

import viper.silver.ast.{CondExp, DecStar, DecTuple, Exp, Function, If, Method, Program, Seqn, Stmt}
import viper.silver.ast.utility.Functions
import viper.silver.ast.utility.Statements.EmptyStmt

class SimpleDecreasePlugin extends SilverPlugin
{
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
        rewriteFunction(function.body.get, heights)
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

  private def rewriteFunction(body: Exp, heights: Map[Function, Int]): Stmt = {
    body match {
      case CondExp(cond, thn, els) =>
        val termCheckInCond = rewriteFunction(cond, heights)
        val thenSt = rewriteFunction(thn, heights)
        val elseSt = rewriteFunction(els, heights)

        val wholeCond: Stmt = if (thenSt == EmptyStmt && elseSt == EmptyStmt) {
          EmptyStmt
        } else {
          If(cond, Seqn(Seq(thenSt), Nil)(body.pos), Seqn(Seq(elseSt), Nil)(body.pos))(body.pos)
        }
        Seqn(Seq(termCheckInCond, wholeCond), Nil)(body.pos)
    }
  }
}
