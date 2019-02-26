
package viper.silver.plugin.termination.proofcode

import viper.silver.ast._
import viper.silver.verifier.errors.AssertFailed
import viper.silver.verifier.{AbstractErrorReason, errors}
import viper.silver.verifier.reasons.AssertionFalse

import scala.collection.immutable.ListMap

class CheckDecreasesSimple(val program: Program, val decreasesMap: Map[Function, DecreasesExp]) extends CheckDecreases[FunctionContext] {

  override def createCheckProgram(): Program = {
    this.clear()

    program.functions.filterNot(f => f.body.isEmpty || getDecreasesExp(f).isInstanceOf[DecreasesStar]).foreach(f => {
      val context = SimpleContext(f)
      val body = transform(f.body.get, context)
      val localVars = neededLocalVars.get(f) match {
        case Some(v) => v.values
        case None => Nil
      }

      val methodBody: Seqn = Seqn(Seq(body), localVars.toIndexedSeq)()
      val methodName = uniqueName(f.name + "_termination_proof")
      val method = Method(methodName, f.formalArgs, Nil, f.pres, Nil, Option(methodBody))()

      methods(methodName) = method
    })

    super.createCheckProgram()
  }

  case class SimpleContext(func: Function) extends FunctionContext

  /**
    * Adds case FuncApp
    * Checks if the termination measure decreases in every function call (to a possibly
    * recursive call)
    *
    * @return a statement representing the expression
    */
  override def transform: PartialFunction[(Exp, FunctionContext), Stmt] = {
    case (callee: FuncApp, context: FunctionContext) =>
      val func = context.func

      val stmts = collection.mutable.ArrayBuffer[Stmt]()

      // check the arguments
      val termChecksOfArgs: Seq[Stmt] = callee.getArgs map (a => transform(a, context))
      stmts.appendAll(termChecksOfArgs)

      val calledFunc = functions(callee.funcname)
      val calleeArgs = callee.getArgs.map(transformExp(_, context))

      if (compareHeights(func, calledFunc)) {
        // In the same cycle. => compare

        // map of parameters in the called function to parameters in the current functions (for substitution)
        val mapFormalArgsToCalledArgs = ListMap(calledFunc.formalArgs.map(_.localVar).zip(calleeArgs): _*)

        val decOrigin = getDecreasesExp(func)
        val decDest = getDecreasesExp(calledFunc)

        assert(decOrigin.isInstanceOf[DecreasesTuple], "Checking a function with DecreasesStar for termination!" +
          "This should not happen!")

        val errTrafo = ErrTrafo({
          case AssertFailed(_, r, c) => TerminationFailed(callee, r, c)
          case d => d
        })

        val reasonTrafoFactory = SimpleReasonTrafoFactory(decOrigin.asInstanceOf[DecreasesTuple])

        val terminationCheck = createTerminationCheck(decOrigin, decDest, mapFormalArgsToCalledArgs, errTrafo, reasonTrafoFactory, context)

        val assertion = terminationCheck

        stmts.appendAll(Seq(assertion))
      } else {
        // not in the same cycle
      }
      Seqn(stmts, Nil)()
    case default => super.transform(default)
  }

  case class SimpleReasonTrafoFactory(offendingNode: DecreasesTuple) extends ReasonTrafoFactory {
    override def createNotDecrease(biggerDec: Seq[Exp], smallerDec: Seq[Exp], context: Context): ReTrafo = {
      ReTrafo({ case AssertionFalse(_) => TerminationNoDecrease(offendingNode, biggerDec, smallerDec) })
    }

    override def createNotBounded(biggerDec: Seq[Exp], context: Context): ReTrafo = {
      ReTrafo({ case AssertionFalse(_) => TerminationNoBound(offendingNode, biggerDec) })
    }

    override def createStar(context: Context): ReTrafo = {
      ReTrafo({ case AssertionFalse(_) => TerminationStar(offendingNode) })
    }
  }
}


case class TerminationNoDecrease(offendingNode: DecreasesTuple, decOrigin: Seq[Exp], decDest: Seq[Exp]) extends AbstractErrorReason {
  val id = "termination.no.decrease"
  override def readableMessage: String = s"Termination measure might not decrease. " +
    s"Assertion (${decDest.mkString(", ")})≺(${decOrigin.mkString(", ")}) might not hold."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoDecrease(this.offendingNode, decOrigin, decDest)
}

case class TerminationNoBound(offendingNode: DecreasesTuple, decExp: Seq[Exp]) extends AbstractErrorReason {
  val id = "termination.no.bound"
  override def readableMessage: String = s"Termination measure might not be bounded. " +
    s"Assertion 0≺(${decExp.mkString(", ")}) might not hold."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoBound(this.offendingNode, decExp)
}

case class TerminationStar(offendingNode: DecreasesTuple) extends AbstractErrorReason {
  val id = "termination.star"
  override def readableMessage = s"Cannot prove termination, if a function with decreasesStar is called."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationStar(this.offendingNode)
}