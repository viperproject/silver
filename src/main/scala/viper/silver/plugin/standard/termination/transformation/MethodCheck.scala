// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.{ContextC, Strategy, Traverse}
import viper.silver.plugin.standard.termination.{DecreasesSpecification, LoopTerminationError, MethodTerminationError}
import viper.silver.verifier.errors.AssertFailed

/**
 * Creates termination checks for methods.
 */
trait MethodCheck extends ProgramManager with DecreasesCheck with NestedPredicates with ErrorReporter {

  private def getMethodDecreasesSpecification(method: String): DecreasesSpecification = {
    program.findMethodOptionally(method) match {
      case Some(f) => DecreasesSpecification.fromNode(f)
      case None => DecreasesSpecification()
    }
  }

  private def getWhileDecreasesSpecification(w: While): DecreasesSpecification = {
    DecreasesSpecification.fromNode(w)
  }

  protected def transformMethod(m: Method): Method = {
    m.body match {
      case Some(body) =>
        val context = MContext(m)
        context.nestedRequired = containsPredicateInstances(DecreasesSpecification.fromNode(m))

        val newBody: Stmt = {
          val stmt: Stmt = methodStrategy(context).execute(body)
          if (context.nestedRequired) {
            addNestedPredicateInformation.execute(stmt)
          } else {
            stmt
          }
        }
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
    ViperStrategy.Context(methodTransformer, context, Traverse.BottomUp).recurseFunc(avoidExpressions)

  private def avoidExpressions: PartialFunction[Node, Seq[AnyRef]] = {
    case _: Exp => Nil
  }

  private def methodTransformer: PartialFunction[(Node, StrategyContext), (Node, StrategyContext)] = {
    case (mc: MethodCall, ctxt) if ctxt.c.mutuallyRecursiveMeths.contains(program.findMethod(mc.methodName)) =>
      // possibly recursive call
      val context = ctxt.c

      getMethodDecreasesSpecification(context.methodName).tuple match {
        case Some(callerTuple) => // check that called method decreases tuple under the methods tuple condition
          val calledMethod = program.findMethod(mc.methodName)
          val mapFormalArgsToCalledArgs = Map(calledMethod.formalArgs.map(_.localVar).zip(mc.args): _*)
          val calleeDec = getMethodDecreasesSpecification(mc.methodName)

          val errTrafo = ErrTrafo({
            case AssertFailed(_, r, c) => MethodTerminationError(mc, r, c)
            case d => d
          })

          val reasonTrafoFactory = ReasonTrafoFactory(callerTuple)

          val oldTupleCondition = callerTuple.condition map(Old(_)())
          val oldTupleExp = callerTuple.tupleExpressions.map(Old(_)())

          val checks = calleeDec.tuple match {
            case Some(calleeTuple) =>
              // reason would be the callee's defined tuple
              val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(calleeTuple)

              val conditionAssertion = createConditionCheck(oldTupleCondition,
                calleeTuple.condition.map(_.replace(mapFormalArgsToCalledArgs)),
                errTrafo, reTrafo)

              val tupleAssertion = createTupleCheck(oldTupleCondition, oldTupleExp,
                calleeTuple.tupleExpressions.map(_.replace(mapFormalArgsToCalledArgs)),
                errTrafo, reasonTrafoFactory)

              Seq(conditionAssertion, tupleAssertion)
            case None =>
              // reason would be the callee's definition
              val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(calledMethod)
              Seq(createConditionCheck(oldTupleCondition, Some(FalseLit()()), errTrafo, reTrafo))
          }

          (Seqn(checks :+ mc, Nil)(mc.pos, NoInfo, NodeTrafo(mc)), ctxt)

        case None => // no tuple is defined, hence no checks are done.
          (mc, ctxt)
      }
    case (mc: MethodCall, ctxt) =>
      // non-recursive call
      val context = ctxt.c

      getMethodDecreasesSpecification(context.methodName).tuple match {
        case Some(methodTuple) => // check that called method terminates under the methods tuple condition
          val calledMethod = program.findMethod(mc.methodName)
          val mapFormalArgsToCalledArgs = Map(calledMethod.formalArgs.map(_.localVar).zip(mc.args): _*)
          val decDest = getMethodDecreasesSpecification(mc.methodName)

          val errTrafo = ErrTrafo({
            case AssertFailed(_, r, c) => MethodTerminationError(mc, r, c)
            case d => d
          })

          val reasonTrafoFactory = ReasonTrafoFactory(methodTuple)
          // reason would be the callee's definition
          val reTrafo = reasonTrafoFactory.generateTerminationConditionFalse(calledMethod)

          val oldTupleCondition = methodTuple.condition map(Old(_)())

          val assertion = createConditionCheck(oldTupleCondition,
            Some(decDest.getTerminationCondition.replace(mapFormalArgsToCalledArgs)),
            errTrafo, reTrafo)

          (Seqn(Seq(assertion, mc), Nil)(mc.pos, NoInfo, NodeTrafo(mc)), ctxt)

        case None => // no tuple is defined, hence no checks are done.
          (mc, ctxt)
      }
    case (w: While, ctxt) =>
      if (containsPredicateInstances(DecreasesSpecification.fromNode(w)))
        ctxt.c.nestedRequired = true

      w.info.getUniqueInfo[Transformed] match {
        case Some(_) => // already traversed this while loop and already added checks to it
          (w, ctxt)
        case None =>
          val context = ctxt.c
          val decWhile = getWhileDecreasesSpecification(w)

          val whileNumber = whileCounter
          whileCounter = whileCounter + 1

          // check that loop terminates under the methods tuple condition (if the loop is entered)
          val terminationCheck =
            getMethodDecreasesSpecification(context.methodName).tuple match {
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

                val assertion = createConditionCheck(Some(requiredTerminationCondition),
                  Some(decWhile.getTerminationCondition),
                  errTrafo, reTrafo)

                Some(assertion)
              case None => None
            }

          val newBody = decWhile.tuple match {
            case Some(whileTuple) =>

              // copy all expression in the decreases tuple to be used later
              // equivalent to labeled old but including variables
              val (oldTupleCondition, conditionAssign): (Exp, Option[LocalVarAssign]) = whileTuple.condition match {
                case Some(condition) =>
                  val conditionCopy =
                    LocalVar(uniqueName(s"old_W${whileNumber}_C"), Bool)(condition.pos, condition.info, condition.errT)
                  val assign = LocalVarAssign(conditionCopy, condition)(condition.pos, condition.info, condition.errT)
                  (conditionCopy, Some(assign))
                case None => (TrueLit()(), None)
              }

              val (oldTupleExps, tupleAssigns): (Seq[Exp], Seq[LocalVarAssign]) = whileTuple.tupleExpressions.zipWithIndex.map(exp_i => {
                val (exp, i) = (exp_i._1, exp_i._2)
                val expCopy =
                  LocalVar(uniqueName(s"old_W${whileNumber}_T$i"), exp.typ)(exp.pos, exp.info, exp.errT)
                val assign = LocalVarAssign(expCopy, exp)(expCopy.pos, expCopy.info, expCopy.errT)
                (expCopy, assign)
              }).unzip

              val assignments = tupleAssigns ++ conditionAssign
              val scopedDeclarations = assignments.map(a => LocalVarDecl(a.lhs.name, a.rhs.typ)())

              val errTrafo = ErrTrafo({
                case AssertFailed(_, r, c) => LoopTerminationError(whileTuple, r, c)
                case d => d
              })

              val reasonTrafoFactory = ReasonTrafoFactory(whileTuple)

              // reason would be the loops's defined tuple
              val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(whileTuple)

              // old tuple condition and
              val requiredTerminationCondition = And(oldTupleCondition, w.cond)()

              // check that tuple condition still holds for the following iteration
              val conditionAssertion = createConditionCheck(Some(requiredTerminationCondition),
                whileTuple.condition,
                errTrafo, reTrafo)
              // check that the tuple decreased
              val tupleCheck = createTupleCheck(Some(requiredTerminationCondition), oldTupleExps,
                whileTuple.tupleExpressions,
                errTrafo, reasonTrafoFactory)

              Seqn(assignments :+ w.body :+ conditionAssertion :+ tupleCheck, scopedDeclarations)()
            case None =>
              // no tuple is defined for the while loop, hence, nothing must be checked for the loop
              w.body
          }

          val newWhile = w.copy(body = newBody)(w.pos, MakeInfoPair(Transformed(), w.info), w.errT)

          val stmts = Seq() ++ terminationCheck :+ newWhile

          (Seqn(stmts, Nil)(), ctxt)
      }
  }

  /**
   * Mark already traversed and transformed nodes.
   * Used for while loops because a while node is potentially traversed twice.
   */
  private final case class Transformed() extends Info {
    override val comment: Seq[String] = Nil

    override val isCached: Boolean = false
  }

  private var whileCounter: Int = 1

  private case class MContext(override val method: Method) extends MethodContext {
    override val methodName: String = method.name
    override val mutuallyRecursiveMeths: Set[Method] = mutuallyRecursiveMethods.find(_.contains(method)).get
  }

  // context used
  private trait MethodContext {
    val method: Method
    val methodName: String

    val mutuallyRecursiveMeths: Set[Method]

    var nestedRequired = false
  }

  private lazy val mutuallyRecursiveMethods: Seq[Set[Method]] = CallGraph.mutuallyRecursiveVertices(methodCallGraph)

  private lazy val methodCallGraph = {
    val graph = new DefaultDirectedGraph[Method, DefaultEdge](classOf[DefaultEdge])

    program.methods.foreach(graph.addVertex)

    def process(m: Method, n: Node): Unit = {
      n visit {
        case MethodCall(m2name, _, _) =>
          graph.addEdge(m, program.findMethod(m2name))
      }
    }

    program.methods.foreach(m => {
      m.body foreach (process(m, _))
    })

    graph
  }
}