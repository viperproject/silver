package viper.silver.plugin.termination

import viper.silver.ast.utility.Functions
import viper.silver.ast.utility.Rewriter.{StrategyBuilder, Traverse}
import viper.silver.ast.{DomainFunc, Exp, FuncApp, Function, Node, Predicate}

/**
  * A basic interface to help create termination checks.
  * Therefore it needs following things in the program:
  * "decreasing" domain function
  * "bounded" domain function
  *
  * It adds dummy function to the program if needed.
  */
trait TerminationCheck extends ProgramCheck with RewriteFunctionBody[SimpleContext] {

  val decreasesMap: Map[Function, DecreaseExp]

  val heights = Functions.heights(program)

  val decreasingFunc: Option[DomainFunc] = program.findDomainFunctionOptionally("decreasing")
  val boundedFunc: Option[DomainFunc] =  program.findDomainFunctionOptionally("bounded")

  /**
    * Replaces all function calls in an expression with calls to dummy functions
    * if they have the same height (possibly mutual recursive).
    * @param exp to be transformed
    * @param context of the transformation
    * @return
    */
  override def transformExp(exp: Exp, context: SimpleContext): Exp = {
    val newExp = StrategyBuilder.Slim[Node]({
      case fa: FuncApp if heights(context.func) == heights(fa.func(program)) =>
        uniqueNameGen(fa)
    }, Traverse.BottomUp)
      .execute(exp)
      .asInstanceOf[Exp]

    super.transformExp(newExp, context)
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
      node.isInstanceOf[FuncApp])

    node match {
      case f: Function =>
        if (neededFunctions.values.exists(_.name == f.name)) {
          neededDomains.values.find(_.name == f.name).get
        } else {
          if (neededFunctions.contains(f.name)) {
            neededFunctions(f.name)
          } else {
            val uniqueFuncName = uniqueName(f.name + "_withoutBody")
            val newFunc = Function(uniqueFuncName, f.formalArgs, f.typ, f.pres, Nil, None, None)(f.pos)
            //functions(uniqueFuncName) = newFunc
            neededFunctions(f.name) = newFunc
            newFunc
          }
        }
      case fa: FuncApp =>
        if (neededFunctions.values.exists(_.name == fa.funcname)) {
          FuncApp(neededFunctions.values.find(_.name == fa.funcname).get, fa.args)(fa.pos)
        } else {
          if (neededFunctions.contains(fa.funcname)) {
            FuncApp(neededFunctions(fa.funcname), fa.args)(fa.pos)
          } else {
            val uniqueFuncName = uniqueName(fa.funcname + "_withoutBody")
            val func = program.findFunction(fa.funcname)
            val newFunc = Function(uniqueFuncName, func.formalArgs, func.typ, Nil, Nil, None, None)(func.pos)
            //functions(uniqueFuncName) = newFunc
            neededFunctions(fa.funcname) = newFunc
            FuncApp(newFunc, fa.args)(fa.pos)
          }
        }
    }
  }
}