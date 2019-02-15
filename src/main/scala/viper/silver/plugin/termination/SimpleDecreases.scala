
package viper.silver.plugin.termination

import viper.silver.ast.{Assert, _}
import viper.silver.verifier.errors.AssertFailed
import viper.silver.verifier.{AbstractErrorReason, AbstractVerificationError, ErrorReason, errors}
import viper.silver.verifier.reasons.AssertionFalse

import scala.collection.immutable.ListMap

class SimpleDecreases(val program: Program, val decreasesMap: Map[Function, DecreasesExp]) extends TerminationCheck[SimpleContext] with NestedPredicate[SimpleContext] {

  override def createCheckProgram(): Program = {
    this.clear()

    // TODO: filter functions with decreasesStar
    program.functions.filterNot(f => f.body.isEmpty || getDecreasesExp(f).isInstanceOf[DecreasesStar]).foreach(f => {
      val context = FunctionContext(f)
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

  case class FunctionContext(func: Function) extends SimpleContext

  /**
    * Adds case FuncApp
    * Checks if the termination measure decreases in every function call (to a possibly
    * recursive call)
    * @return a statement representing the expression
    */
  override def transform: PartialFunction[(Exp, SimpleContext), Stmt] = {
    case (callee: FuncApp, context: SimpleContext) =>
      val func = context.func

      val stmts = collection.mutable.ArrayBuffer[Stmt]()

      val calledFunc = callee.func(program)
      val calleeArgs = callee.getArgs

      // check the arguments
      val termChecksOfArgs: Seq[Stmt] = calleeArgs map (a => transform(a, context))
      stmts.appendAll(termChecksOfArgs)

      if (heights(func) == heights(calledFunc)){
        // In the same cycle. => compare

        // map of parameters in the called function to parameters in the current functions (for substitution)
        val mapFormalArgsToCalledArgs = ListMap(calledFunc.formalArgs.map(_.localVar).zip(calleeArgs):_*)

          val decOrigin = getDecreasesExp(func)
          val decDest = getDecreasesExp(calledFunc)

          val errTrafo = ErrTrafo({
            case AssertFailed(_,r,c) => TerminationFailed(callee, r, c)
            case d => d
          })

          val terminationCheck = createTerminationCheck(decOrigin, decDest, mapFormalArgsToCalledArgs, errTrafo, context)

          val assertion = terminationCheck

          stmts.appendAll(Seq(assertion))
      }else{
        // not in the same cycle
      }
      Seqn(stmts, Nil)()
    case default => super.transform(default)
  }

  /**
    * Creates a termination check
    * @param biggerDec DecreaseExp of the function currently checked
    * @param smallerDec DecreaseExp of the function called
    * @return termination check as a Assert Stmt
    */
  def createTerminationCheck(biggerDec: DecreasesExp, smallerDec: DecreasesExp, argMap: Map[LocalVar, Node], errTrafo: ErrTrafo, context: SimpleContext): Assert = {
    (biggerDec, smallerDec) match {
      case (DecreasesTuple(_,_,_), DecreasesStar(_,_)) =>
        Assert(FalseLit()())(errT = errTrafo)
      case (DecreasesTuple(biggerExp,_,_), DecreasesTuple(smallerExp,_,_)) =>
        // trims to the longest commonly typed prefix
        val (bExp, sExp) = (biggerExp zip smallerExp.map(_.replace(argMap))).takeWhile(exps => exps._1.typ == exps._2.typ).unzip

        val reTBound = ReTrafo({
          case AssertionFalse(_) =>
            TerminationNoBound(biggerDec, bExp)
        })

        val reTDec = ReTrafo({
          case AssertionFalse(_) =>
            TerminationNoDecrease(biggerDec, bExp)
        })

        val checkableBiggerExp = bExp.map({
          case pa: PredicateAccess =>
            assert(locationDomain.isDefined)
            val varOfCalleePred = uniquePredLocVar(pa, context)
            varOfCalleePred
          case unfold: Unfolding => Old(unfold)(unfold.pos)
          case default => default
        })

        val checkableSmallerExp = sExp.map({
          case pa: PredicateAccess =>
            val varOfCalleePred = uniquePredLocVar(pa, context)
            varOfCalleePred
          case default => default
        })

        val check = createTerminationCheckExp(checkableBiggerExp, checkableSmallerExp, reTDec, reTBound)

        Assert(check)(errT = errTrafo)
      case default =>
        assert(false, "Checking a function with DecreasesStar for termination!")
        Assert(FalseLit()())(errT = errTrafo)
    }
  }

  /**
    * Creates Expression to check decrease and bounded of lexicographical order
    * (decreasing(s,b) && bounded(b)) || (s==b && ( (decr...
    * @param biggerExp [b,..] with at least one element
    * @param smallerExp [s,..] same size as biggerExp
    * @return expression
    */
  def createTerminationCheckExp(biggerExp: Seq[Exp], smallerExp: Seq[Exp], decrReTrafo: ReTrafo, boundReTrafo: ReTrafo): Exp = {

    val paramTypesDecr = decreasingFunc.get.formalArgs map (_.typ)
    val argTypeVarsDecr = paramTypesDecr.flatMap(p => p.typeVariables)
    val paramTypesBound = boundedFunc.get.formalArgs map (_.typ)
    val argTypeVarsBound = paramTypesBound.flatMap(p => p.typeVariables)


    def createExp(biggerExp: Seq[Exp], smallerExp: Seq[Exp]): Exp = {
      assert(biggerExp.size == smallerExp.size)
      val bigger = biggerExp.head
      val smaller = smallerExp.head
      val dec = DomainFuncApp(decreasingFunc.get,
        Seq(smaller, bigger),
        ListMap(argTypeVarsDecr.head -> smaller.typ,
          argTypeVarsDecr.last -> bigger.typ))(errT = decrReTrafo)

      val bound = DomainFuncApp(boundedFunc.get,
        Seq(bigger),
        ListMap(argTypeVarsDecr.head -> bigger.typ,
          argTypeVarsDecr.last -> bigger.typ
        ))(errT = boundReTrafo)

      val andPart = And(dec, bound)()

      if (biggerExp.size == 1){
        // no next elements
        andPart
      }else{
        val eq = EqCmp(smaller, bigger)(errT = decrReTrafo)
        val next = createExp(biggerExp.tail, smallerExp.tail)
        val nextPart = And(eq, next)()
        Or(andPart, nextPart)()
      }
    }
    createExp(biggerExp, smallerExp)
  }
}

trait SpecialContext extends SimpleContext

case class TerminationFailed(offendingNode: FuncApp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "termination.failed"
  val text = s"Function might not terminate."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationFailed(this.offendingNode, this.reason)
  def withReason(r: ErrorReason) = TerminationFailed(offendingNode, r)
}

case class TerminationNoDecrease(offendingNode: DecreasesExp, decOrigin: Seq[Exp]) extends AbstractErrorReason {
  val id = "termination.no.decreasing"
  override def readableMessage = s"Termination measure (${decOrigin.mkString(", ")}) might not decrease."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoDecrease(this.offendingNode, decOrigin)
}

case class TerminationNoBound(offendingNode: DecreasesExp, decExp: Seq[Exp]) extends AbstractErrorReason {
  val id = "termination.no.bound"
  override def readableMessage = s"Termination measure (${decExp.mkString(", ")}) might not be bounded."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoBound(this.offendingNode, decExp)
}