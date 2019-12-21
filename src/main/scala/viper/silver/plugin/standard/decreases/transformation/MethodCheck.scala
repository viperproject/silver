package viper.silver.plugin.standard.decreases.transformation

import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.{ContextC, Strategy, Traverse}
import viper.silver.plugin.standard.decreases.{DecreasesContainer, DecreasesTuple, LoopTerminationError, MethodTerminationError}
import viper.silver.verifier.errors.AssertFailed

import scala.collection.immutable.ListMap

/**
  * Creates termination checks for methods.
  */
trait MethodCheck extends ProgramManager with DecreasesCheck with PredicateInstanceManager with ErrorReporter {

  /**
    * Checks if two methods call each other recursively (also indirect) (same cluster)
    * @param m1 method one
    * @param m2 method two
    * @return true iff in same cluster
    */
  def sameCluster(m1: String, m2: String): Boolean = {
    val method1 = program.findMethod(m1)
    val method2 = program.findMethod(m2)
    MethodsHelper.getMethodCluster(method1, program).contains(method2)
  }

  /**
    * @param method name
    * @return DecreasesExp defined by the user if exists, otherwise a DecreasesTuple containing the methods parameter.
    */
  def getMethodDecreasesContainer(method: String): DecreasesContainer = {
    transformPredicateInstances(
      program.methods.find(_.name == method) match {
        case Some(f) => DecreasesContainer.fromNode(f)
        case None => DecreasesContainer()
      }
    )
  }

  def getWhileDecreasesContainer(w: While): DecreasesContainer = {
    transformPredicateInstances(
      DecreasesContainer.fromNode(w)
    )
  }

  /**
    * Transforms all the methods in the (original) program to contain termination checks.
    */
  protected def transformMethods(): Unit = {
    program.methods.foreach(m => {
      val method = transformMethod(m)
      methods.update(m.name, method)
    })
  }

  private def transformMethod(m: Method): Method = {
    m.body match {
      case Some(body) =>
        val context = MContext(m)

        val newBody: Stmt = methodStrategy(context).execute(body)
        val methodBody: Seqn = Seqn(Seq(newBody), Nil)()
        val method = m.copy(body = Option(methodBody))(m.pos, m.info, m.errT)
        method
      case None => m
    }
  }

  private type StrategyContext = ContextC[Node, MethodContext]

  /**
    * @return Strategy to be used to transform a methods body.
    */
  private def methodStrategy(context: MethodContext): Strategy[Node, StrategyContext] =
    // BottomUp traversal does not work because the original While node is required
    // to obtain the associated DecreasesContainer
    ViperStrategy.Context(methodTransformer, context, Traverse.BottomUp).recurseFunc(avoidExpressions)

  private def avoidExpressions: PartialFunction[Node, Seq[AnyRef]] = {
    case _: Exp => Nil
  }

  private def methodTransformer: PartialFunction[(Node, StrategyContext), (Node, StrategyContext)] = {
    case (mc: MethodCall, ctxt) if sameCluster(mc.methodName, ctxt.c.methodName) =>
      // possibly recursive call
      val context = ctxt.c

      getMethodDecreasesContainer(context.methodName).tuple match {
        case Some(callerTuple) => // check that called method decreases tuple under the methods tuple condition
          val calledMethod = methods(mc.methodName)
          val mapFormalArgsToCalledArgs = ListMap(calledMethod.formalArgs.map(_.localVar).zip(mc.args): _*)
          val calleeDec = getMethodDecreasesContainer(mc.methodName)

          val errTrafo = ErrTrafo({
            case AssertFailed(_, r, c) => MethodTerminationError(mc, r, c)
            case d => d
          })

          val reasonTrafoFactory = ReasonTrafoFactory(callerTuple)

          val oldCondition = Old(callerTuple.getCondition)()
          val oldTupleExp = callerTuple.tupleExpressions.map(Old(_)())
          val oldTuple = DecreasesTuple(oldTupleExp, Some(oldCondition))(callerTuple.pos, callerTuple.info, callerTuple.errT)

          val checks = calleeDec.tuple match {
            case Some(calleeTuple) =>
              // reason would be the callee's defined tuple
              val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(calleeTuple)

              val conditionAssertion = createConditionCheck(oldCondition, calleeTuple.getCondition, mapFormalArgsToCalledArgs, errTrafo, reTrafo)
              val tupleAssertion = createTupleCheck(oldTuple, calleeTuple, mapFormalArgsToCalledArgs, errTrafo, reasonTrafoFactory)
              Seq(conditionAssertion, tupleAssertion)
            case None =>
              // reason would be the callee's definition
              val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(calledMethod)
              Seq(createConditionCheck(oldCondition, FalseLit()(), Map(), errTrafo, reTrafo))
          }

          // do not traverse method call again
          (Seqn(checks :+ mc, Nil)(mc.pos, NoInfo, NodeTrafo(mc)), ctxt)

        case None => // no tuple is defined, hence no checks are done.
          (mc, ctxt)
      }
    case (mc: MethodCall, ctxt) if !sameCluster(mc.methodName, ctxt.c.methodName) =>
      val context = ctxt.c

      getMethodDecreasesContainer(context.methodName).tuple match {
        case Some(methodTuple) => // check that called method terminates under the methods tuple condition
          val calledMethod = methods(mc.methodName)
          val mapFormalArgsToCalledArgs = ListMap(calledMethod.formalArgs.map(_.localVar).zip(mc.args): _*)
          val decDest = getMethodDecreasesContainer(mc.methodName)

          val errTrafo = ErrTrafo({
            case AssertFailed(_, r, c) => MethodTerminationError(mc, r, c)
            case d => d
          })

          val reasonTrafoFactory = ReasonTrafoFactory(methodTuple)
          // reason would be the callee's definition
          val reTrafo = reasonTrafoFactory.generateTerminationConditionFalse(calledMethod)

          val oldCondition = Old(methodTuple.getCondition)()
          val assertion = createConditionCheck(oldCondition, decDest.terminationCondition, mapFormalArgsToCalledArgs, errTrafo, reTrafo)

          // do not traverse method call again
          (Seqn(Seq(assertion, mc), Nil)(mc.pos, NoInfo, NodeTrafo(mc)), ctxt)

        case None => // no tuple is defined, hence no checks are done.
          (mc, ctxt)
      }
    case (w: While, ctxt) =>
      val context = ctxt.c
      val decWhile = getWhileDecreasesContainer(w)

      val whileNumber = whileCounter
      whileCounter = whileCounter + 1

      // check that loop terminates under the methods tuple condition (if the loop is entered)
      val terminationCheck =
        getMethodDecreasesContainer(context.methodName).tuple match {
          case Some(methodTuple) =>

            val errTrafo = ErrTrafo({
              case AssertFailed(_, r, c) => MethodTerminationError(w, r, c)
              case d => d
            })

            val reasonTrafoFactory = ReasonTrafoFactory(methodTuple)
            // reason would be the loop's definition
            val reTrafo = reasonTrafoFactory.generateTerminationConditionFalse(w)

            val oldCondition = Old(methodTuple.getCondition)()
            val requiredTerminationCondition = And(oldCondition, w.cond)()

            val assertion = createConditionCheck(requiredTerminationCondition, decWhile.terminationCondition, Map(), errTrafo, reTrafo)

            Some(assertion)
          case None => None
        }

      val newBody = decWhile.tuple match {
        case Some(whileTuple) =>
          // copy all expression in the decreases tuple to be used later
          // equivalent to labeled old but including variables

          val (oldCondition, conditionAssign): (Exp, Option[LocalVarAssign]) = whileTuple.condition match {
            case Some(condition) =>
              // TODO: check var name uniqueness
              val conditionCopy =
                LocalVar(s"W${whileNumber}_C", Bool)(condition.pos, condition.info, condition.errT)
              val assign = LocalVarAssign(conditionCopy, condition)(condition.pos, condition.info, condition.errT)
              (conditionCopy, Some(assign))
            case None => (TrueLit()(), None)
          }

          val (oldTupleExps, tupleAssigns): (Seq[Exp], Seq[LocalVarAssign]) = whileTuple.tupleExpressions.zipWithIndex.map(exp_i => {
            val (exp, i) = (exp_i._1, exp_i._2)
            // TODO: check var name uniqueness
            val expCopy =
              LocalVar(s"W${whileNumber}_T$i", exp.typ)(exp.pos, exp.info, exp.errT)
            val assign = LocalVarAssign(expCopy, exp)(expCopy.pos, expCopy.info, expCopy.errT)
            (expCopy, assign)
          }).unzip

          val oldDecreasesTuple = DecreasesTuple(oldTupleExps, Some(oldCondition))()
          val assignments = tupleAssigns ++ conditionAssign
          val scopedDeclarations = assignments.map(a => LocalVarDecl(a.lhs.name, a.rhs.typ)())

          val errTrafo = ErrTrafo({
            case AssertFailed(_, r, c) => LoopTerminationError(whileTuple, r, c)
            case d => d
          })

          val reasonTrafoFactory = ReasonTrafoFactory(whileTuple)

          // reason would be the loops's defined tuple
          val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(whileTuple)

          // check that tuple condition still holds for the following iteration
          val requiredTerminationCondition = And(oldCondition, w.cond)()
          val conditionAssertion = createConditionCheck(requiredTerminationCondition, whileTuple.getCondition, Map(), errTrafo, reTrafo)
          // check that the tuple decreased
          val tupleCheck = createTupleCheck(oldDecreasesTuple, whileTuple, Map(), errTrafo, reasonTrafoFactory)

          Seqn(assignments :+ w.body :+ conditionAssertion :+ tupleCheck, scopedDeclarations)()
        case None =>
          // no tuple is defined for the while loop, hence, nothing must be checked for the loop
          w.body

      }

      val newWhile = w.copy(body = newBody)(w.pos, w.info, w.errT)

      // do not traverse while loop call again
      val stmts = Seq() ++ terminationCheck :+ newWhile

      (Seqn(stmts, Nil)(), ctxt)
    case (unfold: Unfold, ctxt) =>
      // do not traverse unfold with nested relations again
      (generateUnfoldNested(unfold.acc), ctxt)
  }

  private var whileCounter: Int = 1

  private case class MContext (override val method: Method) extends MethodContext {
    override val methodName: String = method.name
  }

  // context used
  private trait MethodContext {
    val method: Method
    val methodName: String
  }
}