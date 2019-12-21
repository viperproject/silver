// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.decreases.transformation

import org.jgrapht.alg.connectivity.KosarajuStrongConnectivityInspector
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.{Bool, CondExp, ErrTrafo, Exp, FalseLit, FuncApp, Function, Inhale, LocalVarDecl, Method, Node, NodeTrafo, Old, Result, Seqn, Stmt, Unfolding}
import viper.silver.plugin.standard.decreases.{DecreasesContainer, DecreasesTuple, FunctionTerminationError}
import viper.silver.verifier.errors.AssertFailed

import scala.collection.JavaConverters._


trait FunctionCheck extends ProgramManager with DecreasesCheck with ExpTransformer with PredicateInstanceManager with ErrorReporter {

  /**
    * This function should be used to access all the DecreasesContainer
    * @param functionName for which the decreases clauses are defined
    * @return the defined DecreasesContainer
    */
  def getFunctionDecreasesContainer(functionName: String): DecreasesContainer = {
    transformPredicateInstances(
      program.findFunctionOptionally(functionName) match {
        case Some(f) => DecreasesContainer.fromNode(f)
        case None => DecreasesContainer()
      }
    )
  }

  /**
   * For each function in the (original) program new methods are added, which contain termination checks.
   */
  protected def transformFunctions(): Unit = {
    program.functions.foreach(f => {
      getFunctionDecreasesContainer(f.name) match {
        case DecreasesContainer(Some(_), _, _) => generateProofMethod(f)
        case _ => // if no decreases tuple is defined do nothing
      }
    })
  }

  /**
   * generates a termination proof methods for a given function and adds it to the program
   * @param f function
   */
  private def generateProofMethod(f: Function): Unit ={
    if (f.body.nonEmpty) {
      // method proving termination of the functions body.
      val proofMethodName = uniqueName(f.name + "_termination_proof")

      val context = FContext(f)

      val proofMethodBody = transformExp(f.body.get, context)

      val proofMethod = Method(proofMethodName, f.formalArgs, Nil, f.pres, Nil,
        Option(Seqn(Seq(proofMethodBody), Nil)()))()

      // add method to the program
      methods(proofMethodName) = proofMethod
    }

    if (f.posts.nonEmpty) {
      // method proving termination of postconditions.
      val proofMethodName = uniqueName(f.name + "_posts_termination_proof")
      val context = FContext(f)

      val resultVariableName = "$result"
      val resultVariable = LocalVarDecl(resultVariableName, f.typ)(f.result.pos, f.result.info, NodeTrafo(f.result))

      // replace all Result nodes with the result variable.
      val posts = f.posts.map(p => ViperStrategy.Slim({
        case Result(t) => resultVariable.localVar
      }, Traverse.BottomUp).execute[Exp](p))

      // after the termination checks assume the postcondition.
      val proofMethodBody = posts.map(p => {
        val postCheck = transformExp(p, context)
        val inhale = Inhale(p)()
        Seqn(Seq(postCheck, inhale), Nil)()
      })

      val proofMethod = Method(proofMethodName, f.formalArgs, Nil, f.pres, Nil,
        Option(Seqn(proofMethodBody, Seq(resultVariable))()))()

      methods(proofMethodName) = proofMethod
    }

    if (f.pres.nonEmpty) {
      val proofMethodName = uniqueName(f.name + "_pres_termination_proof")
      val context = DummyFunctionContext(f)

      val proofMethodBody = f.pres.map(p => {
        // function preconditions possibly contains inhale exhale expressions
        val pIn = p.whenInhaling
        val pEx = p.whenExhaling

        val inhale = if (pIn == pEx) {
          Inhale(p)()
        } else {
          Inhale(CondExp(context.conditionInEx.get.localVar, pIn, pEx)())()
        }

        val presCheck = transformExp(p, context)
        Seqn(Seq(inhale, presCheck), Nil)()
      })

      val proofMethod = Method(proofMethodName, f.formalArgs, Nil, Nil, Nil,
        Option(Seqn(proofMethodBody, Seq(context.conditionInEx.get))()))()

      methods(proofMethodName) = proofMethod
    }
  }


  /**
    * Adds case FuncApp
    * Checks if the termination measure decreases in every function call (to a possibly
    * recursive call)
    *
    * @return a statement representing the expression
    */
  override def transformExp: PartialFunction[(Exp, ExpressionContext), Stmt] = {
    case (functionCall: FuncApp, context: FunctionContext) =>
      val stmts = collection.mutable.ArrayBuffer[Stmt]()

      // check the arguments
      val termChecksOfArgs: Seq[Stmt] = functionCall.getArgs map (a => transformExp(a, context))
      stmts.appendAll(termChecksOfArgs)


      getFunctionDecreasesContainer(context.functionName).tuple match {
        case Some(callerTuple) =>
          val caller = context.function
          val callee = functions(functionCall.funcname)
          val calleeArgs = functionCall.getArgs

          // map of parameters in the called function to parameters in the current functions (for substitution)
          val mapFormalArgsToCalledArgs = Map(callee.formalArgs.map(_.localVar).zip(calleeArgs): _*)
          val calleeDec = getFunctionDecreasesContainer(callee.name)

          if (context.mutuallyRecursiveFuncs.contains(callee)) {
            // potentially recursive call

            // error transformer
            val errTrafo = ErrTrafo({
              case AssertFailed(_, r, c) => FunctionTerminationError(functionCall, r, c)
              case d => d
            })

            val reasonTrafoFactory = ReasonTrafoFactory(callerTuple)

            // old expressions are needed to access predicates which were unfolded but now have to be accessed
            // e.g. in the tuple or the condition
            val oldTupleCondition = Old(callerTuple.getCondition)()
            val oldTupleExpressions = callerTuple.tupleExpressions.map(Old(_)())
            val oldDecreasesTuple = DecreasesTuple(oldTupleExpressions, Some(oldTupleCondition))()

            val checks = calleeDec.tuple match {
              case Some(calleeTuple) =>
                // reason would be the callee's defined tuple
                val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(calleeTuple)

                val conditionAssertion = createConditionCheck(oldTupleCondition, calleeTuple.getCondition, mapFormalArgsToCalledArgs, errTrafo, reTrafo)
                val tupleAssertion = createTupleCheck(oldDecreasesTuple, calleeTuple, mapFormalArgsToCalledArgs, errTrafo, reasonTrafoFactory)
                Seq(conditionAssertion, tupleAssertion)
              case None =>
                // reason would be the callee's definition
                val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(callee)
                Seq(createConditionCheck(oldTupleCondition, FalseLit()(), Map(), errTrafo, reTrafo))
            }

            stmts.appendAll(checks)

          } else {
            // call is not recursive

            val errTrafo = ErrTrafo({
              case AssertFailed(_, r, c) => FunctionTerminationError(functionCall, r, c)
              case d => d
            })

            val reasonTrafoFactory = ReasonTrafoFactory(callerTuple)

            // reason would be the callee's definition
            val reTrafo = reasonTrafoFactory.generateTerminationConditionFalse(callee)

            val oldCondition = Old(callerTuple.getCondition)()
            val assertion = createConditionCheck(oldCondition, calleeDec.terminationCondition, mapFormalArgsToCalledArgs, errTrafo, reTrafo)

            stmts.append(assertion)
          }

            case None =>
          // no tuple is defined, hence, nothing must be checked
          // should not happen
          EmptyStmt
      }
      Seqn(stmts, Nil)()
    case (unfolding: Unfolding, context: FunctionContext) =>
      val bodyStmts = transformExp(unfolding.body, context)
      bodyStmts match {
        case EmptyStmt => // nothing was created for the body
          EmptyStmt
        case stmts =>
          val unfold = generateUnfoldNested(unfolding.acc)
          Seqn(Seq(unfold, stmts), Nil)()
      }
    case default => super.transformExp(default)
  }

  // context creator
  private case class FContext(override val function: Function) extends FunctionContext {
    override val conditionInEx: Option[LocalVarDecl]  = Some(LocalVarDecl("$condInEx", Bool)())
    override val functionName: String = function.name
    override val mutuallyRecursiveFuncs: Set[Function] = mutuallyRecursiveFunctions.find(_.contains(function)).get
  }
  private case class DummyFunctionContext(override val function: Function) extends FunctionContext {
    override val conditionInEx: Option[LocalVarDecl] = Some(LocalVarDecl("$condInEx", Bool)())
    override val functionName: String = function.name

    override val mutuallyRecursiveFuncs: Set[Function] = Set()
  }

  // context used to create proof method
  private trait FunctionContext extends ExpressionContext {
    val function: Function
    val functionName: String
    override val unsupportedOperationException: Boolean = true

    val mutuallyRecursiveFuncs: Set[Function]
  }


  private lazy val mutuallyRecursiveFunctions: Seq[Set[Function]] = {
    val stronglyConnected = new KosarajuStrongConnectivityInspector(functionCallGraph)
    val c = stronglyConnected.stronglyConnectedSets()
    c.asScala.map(_.asScala.toSet)
  }

  private lazy val functionCallGraph: DefaultDirectedGraph[Function, DefaultEdge] = {
    val graph = new DefaultDirectedGraph[Function, DefaultEdge](classOf[DefaultEdge])

    program.functions.foreach(graph.addVertex)

    def process(f: Function, n: Node) {
      n visit {
        case app: FuncApp =>
          graph.addEdge(f, app.func(program))
      }
    }

    program.functions.foreach(f => {
      f.pres ++ f.posts ++ f.body foreach (process(f, _))
    })

    graph
  }
}