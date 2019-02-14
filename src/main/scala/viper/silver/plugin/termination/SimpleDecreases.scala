
package viper.silver.plugin.termination

import viper.silver.ast.{Assert, _}
import viper.silver.verifier.errors.AssertFailed
import viper.silver.verifier.{AbstractErrorReason, AbstractVerificationError, ErrorReason, errors}
import viper.silver.verifier.reasons.AssertionFalse

import scala.collection.immutable.ListMap

class SimpleDecreases(val program: Program, val decreasesMap: Map[Function, DecreaseExp]) extends TerminationCheck[SimpleContext] with NestedPredicate[SimpleContext] {

  override def createCheckProgram(): Program = {
    this.clear()

    program.functions.filter(_.body.nonEmpty).foreach(f => {
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

          val decOrigin = decreasesMap.get(func)
          val decDest = decreasesMap.get(calledFunc)

          if (decOrigin.isEmpty || decDest.isEmpty){
            // TODO: Which policies?

          }else{

            // none is empty
            //val formalArgs: Seq[LocalVar] = func.formalArgs map (_.localVar)
            var neededArgAssigns: Seq[Stmt] = Nil //Needed for decreasing predicates

            val comparableDec =
              (decOrigin.get.subExps zip decDest.get.subExps.map(_.replace(mapFormalArgsToCalledArgs)))
                .takeWhile(exps => exps._1.typ == exps._2.typ)
                .unzip

            val biggerExpression = comparableDec._1 map {
            case pap: PredicateAccess =>
              assert(locationDomain.isDefined)
              val varOfCalleePred = uniquePredLocVar(pap, context)

              //neededArgAssigns :+= generateAssign(pap, varOfCalleePred)
              varOfCalleePred
              case unfold: Unfolding => Old(unfold)(unfold.pos)
              case default => default
            }

            val smallerExpressions = comparableDec._2 map {
              case pap: PredicateAccess =>
                val varOfCalleePred = uniquePredLocVar(pap, context)

                //neededArgAssigns :+= generateAssign(pap, varOfCalleePred)
                varOfCalleePred
              case decC => decC
            }

            val reTBound = ReTrafo({
              case AssertionFalse(_) =>
                TerminationNoBound(callee, biggerExpression)
            })

            val reTDec = ReTrafo({
              case AssertionFalse(_) =>
                TerminationNoDecrease(callee, biggerExpression)
            })

            val errTrafo = ErrTrafo({
              case AssertFailed(_,r,c) => TerminationFailed(decOrigin.get, r, c)
              case d => d
            })

            val terminationCheck = createTerminationCheck(biggerExpression.map(transformExp(_, context)), smallerExpressions.map(transformExp(_, context)), reTDec, reTBound)

            val assertion = Assert(terminationCheck)(callee.pos, NoInfo, errTrafo)

            stmts.appendAll(neededArgAssigns :+ assertion)
          }
      }else{
        // not in the same cycle
      }
      Seqn(stmts, Nil)()
    case default => super.transform(default)
  }

  /**
    * Creates Expression to check decrease and bounded of lexicographical order
    * (decreasing(s,b) && bounded(b)) || (s==b && ( (decr...
    * @param biggerExp [b,..] with at least one element
    * @param smallerExp [s,..] same size as biggerExp
    * @return expression
    */
  def createTerminationCheck(biggerExp: Seq[Exp], smallerExp: Seq[Exp], decrReTrafo: ReTrafo, boundReTrafo: ReTrafo): Exp = {

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

case class TerminationFailed(offendingNode: DecreaseExp, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "termination.failed"
  val text = s"Function might not terminate."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationFailed(this.offendingNode, this.reason)
  def withReason(r: ErrorReason) = TerminationFailed(offendingNode, r)
}

case class TerminationNoDecrease(offendingNode: FuncApp, decOrigin: Seq[Exp]) extends AbstractErrorReason {
  val id = "termination.no.decreasing"
  override def readableMessage = s"Termination measure (${decOrigin.mkString(", ")}) might not decrease when calling $offendingNode ${offendingNode.pos}."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoDecrease(offendingNode.asInstanceOf[FuncApp], decOrigin)
}

case class TerminationNoBound(offendingNode: FuncApp, decExp: Seq[Exp]) extends AbstractErrorReason {
  val id = "termination.no.bound"
  override def readableMessage = s"Termination measure (${decExp.mkString(", ")}) might not be bounded when calling $offendingNode ${offendingNode.pos}."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = TerminationNoBound(offendingNode.asInstanceOf[FuncApp], decExp)
}