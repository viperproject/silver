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
trait TerminationCheck[C <: SimpleContext] extends ProgramCheck with RewriteFunctionBody[C] {

  val decreasesMap: Map[Function, DecreasesExp]

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
  override def transformExp(exp: Exp, context: C): Exp = {
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
        if (functions.values.exists(_.name == f.name)) {
          domains.values.find(_.name == f.name).get
        } else {
          if (functions.contains(f.name)) {
            functions(f.name)
          } else {
            val uniqueFuncName = uniqueName(f.name + "_withoutBody")
            val newFunc = Function(uniqueFuncName, f.formalArgs, f.typ, f.pres, Nil, None, None)(f.pos)
            //functions(uniqueFuncName) = newFunc
            functions(f.name) = newFunc
            newFunc
          }
        }
      case fa: FuncApp =>
        if (functions.values.exists(_.name == fa.funcname)) {
          FuncApp(functions.values.find(_.name == fa.funcname).get, fa.args)(fa.pos)
        } else {
          if (functions.contains(fa.funcname)) {
            FuncApp(functions(fa.funcname), fa.args)(fa.pos)
          } else {
            val uniqueFuncName = uniqueName(fa.funcname + "_withoutBody")
            val func = program.findFunction(fa.funcname)
            val newFunc = Function(uniqueFuncName, func.formalArgs, func.typ, Nil, Nil, None, None)(func.pos)
            //functions(uniqueFuncName) = newFunc
            functions(fa.funcname) = newFunc
            FuncApp(newFunc, fa.args)(fa.pos)
          }
        }
    }
  }
}