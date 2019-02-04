
package viper.silver.plugin.termination

import viper.silver.FastMessaging
import viper.silver.ast.{Assert, _}
import viper.silver.ast.utility.{Consistency, Functions}
import viper.silver.ast.utility.Rewriter.{StrategyBuilder, Traverse}
import viper.silver.verifier.errors.AssertFailed
import viper.silver.verifier.{AbstractErrorReason, AbstractVerificationError, ErrorReason, errors}
import viper.silver.verifier.reasons.AssertionFalse

import scala.collection.immutable.ListMap

class SimpleDecreases(val program: Program, val decreasesMap: Map[Function, DecreaseExp]) extends TerminationCheck with RewriteFunctionBody[SimpleContext] with RewritePredicateBody {

  private val heights = Functions.heights(program)

  def createCheckProgram(): Program = {
    this.clear()

    program.functions.filter(_.body.nonEmpty).foreach(f => {
      val context = FunctionContext(f)
      val methodBody: Seqn = Seqn(Seq(transform(f.body.get, context)), Nil)()
      val methodName = uniqueName(f.name + "_termination_proof")
      val method = Method(methodName, f.formalArgs, Nil, f.pres, Nil, Option(methodBody))()

      neededMethods(methodName) = method
    })

    val m = neededMethods.values.toSeq
    val f = neededFunctions.values.toSeq
    val d = if(neededLocFunctions.nonEmpty){
      assert(locationDomain.isDefined)
      val domainsWLoc = program.domains.filterNot(_ == locationDomain.get)
      val newLocDom = Domain(locationDomain.get.name,
        neededLocFunctions.values.toSeq,
        locationDomain.get.axioms,
        locationDomain.get.typVars)(locationDomain.get.pos, locationDomain.get.info, locationDomain.get.errT)
      domainsWLoc ++ Seq(newLocDom) ++ neededDomains.values.toSeq
    }else{
      Nil
    }

    Program(program.domains ++ d,
      program.fields,
      program.functions ++ f,
      program.predicates,
      program.methods ++ m)(program.pos, program.info, program.errT)
  }

  case class FunctionContext(func: Function) extends SimpleContext

  /**
    * Adds cases PredicateAccessPredicate and FuncApp
    * @return a statement representing the expression
    */
  override def transform: PartialFunction[(Exp, SimpleContext), Stmt] = {
    case (pap: PredicateAccessPredicate, c: SimpleContext) =>
      val func = c.func
      val permChecks = transform(pap.perm, c)
      //Add the nested-assumption if the predicate has another predicate inside of its body
      func.decs match {
        case Some(DecTuple(_)) =>
          val pred: Predicate = program.findPredicate(pap.loc.predicateName)

          pred.body match {
            case Some(body) =>
              if (locationDomain.isDefined && nestedFunc.isDefined) {
                val formalArgs = pred.formalArgs map (_.localVar)
                //Generate nested-assumption
                val predBody = rewritePredBodyAsExp(body.replace(ListMap(formalArgs.zip(pap.loc.args):_*)), pap)
                Seqn(Seq(permChecks, predBody), Nil)(body.pos)
              } else {
                if (locationDomain.isEmpty) {
                  Consistency.messages ++= FastMessaging.message(
                    func, "missing location-domain")
                }
                if (nestedFunc.isEmpty) {
                  Consistency.messages ++= FastMessaging.message(
                    func, "missing nested-relation")
                }
                permChecks
              }
            //Predicate has no body
            case None => permChecks
          }
        //No decreasing clause
        case _ => permChecks
      }
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
              /* TODO:
            case pap: PredicateAccessPredicate =>
              assert(locationDomain.isDefined)
              val varOfCalleePred = uniquePredLocVar(pap.loc)

              neededArgAssigns :+= generateAssign(pap, varOfCalleePred)
              varOfCalleePred
              */
              case unfold: Unfolding => Old(unfold)(unfold.pos)
              case default => default
            }
            val smallerExpressions = comparableDec._2 map {
              /* TODO
              case pap: PredicateAccessPredicate =>
                val varOfCalleePred = uniquePredLocVar(pap.loc)

                neededArgAssigns :+= generateAssign(pap, varOfCalleePred)
                varOfCalleePred
                */
              case decC => decC
            }

            val info = SimpleInfo(Seq("TerminationCheck "))

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

            val terminationCheck = createTerminationCheck(biggerExpression, smallerExpressions, reTDec, reTBound)

            val assert = Assert(terminationCheck)(callee.pos, info, errTrafo)

            stmts.appendAll(neededArgAssigns :+ assert)
          }
      }else{
        // not in the same cycle
      }
      Seqn(stmts, Nil)()
    case default => super.transform(default)
  }

  /**
    * Replaces all functions (FuncApp) in an expression with their corresponding dummy-functions
    *
    * StrategyBuilder is used instead of replace,
    * due to the fact that the replace-method uses the Innermost-Traverse order, which stops after the first rewrite.
    * With the StrategyBuilder we can use the bottomUp-traverse-order which e.g. rewrites also function arguments.
    *
    * @param exp the expression which should be investigated
    * @return the same expression but with all functions replaced
    */
  override def transformExp(exp: Exp, context: SimpleContext): Exp = {
    StrategyBuilder.Slim[Node]({
      case fa: FuncApp if heights(context.func) == heights(fa.func(program)) =>
        uniqueNameGen(fa)
    }, Traverse.BottomUp)
      .execute(exp)
      .asInstanceOf[Exp]
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

  def createTerminationCheck(biggerExp: Seq[Exp], smallerExp: Seq[Exp], decrReTrafo: ReTrafo, boundReTrafo: ReTrafo): Exp = {

    val paramTypesDecr = decreasingFunc.get.formalArgs map (_.typ)
    val argTypeVarsDecr = paramTypesDecr.flatMap(p => p.typeVariables)
    val paramTypesBound = boundedFunc.get.formalArgs map (_.typ)
    val argTypeVarsBound = paramTypesBound.flatMap(p => p.typeVariables)

    /**
      *
      * bounded(b) && (decreasing(s,b) || (s==b && ( bound...
      * TODO: better be: (decreasing(s,b) && bounded(b)) || (s==b && ( (decr...
      * @param biggerExp [b,..] with at least one element
      * @param smallerExp [s,..] same size as biggerExp
      * @return expression
      */
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

trait SimpleContext extends Context{
  def func: Function
}

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