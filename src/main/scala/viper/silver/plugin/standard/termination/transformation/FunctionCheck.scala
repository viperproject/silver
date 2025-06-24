// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import viper.silver.ast.utility.QuantifiedPermissions.SourceQuantifiedPermissionAssertion
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.utility.{Simplifier, ViperStrategy}
import viper.silver.ast.{And, Bool, ErrTrafo, Exp, FalseLit, FieldAccessPredicate, FullPerm, FuncApp, Function, Implies, LocalVarDecl, Method, NoPerm, Node, NodeTrafo, Old, PermLtCmp, PredicateAccessPredicate, Result, Seqn, Stmt, TrueLit, Unfold, Unfolding, WildcardPerm}
import viper.silver.plugin.standard.termination.{DecreasesSpecification, FunctionTerminationError}
import viper.silver.verifier.errors.AssertFailed

trait FunctionCheck extends ProgramManager with DecreasesCheck with ExpTransformer with NestedPredicates with ErrorReporter {

  // Variable name for the result variable used in post condition termination checks
  private lazy val resultVariableName = uniqueName("$result")

  // Variable (name) used to distinguish between inhale and exhale branches (required for InhaleExhale Expression)
  private lazy val condInExVariableName = uniqueName("$condInEx")

  private def getFunctionDecreasesSpecification(functionName: String): DecreasesSpecification = {
    program.findFunctionOptionally(functionName) match {
      case Some(f) => DecreasesSpecification.fromNode(f)
      case None => DecreasesSpecification()
    }
  }

  /**
   * generates a termination proof methods for a given function and adds it to the program
   *
   * @param f function
   */
  protected def generateProofMethods(f: Function, respectFuncPermAmounts: Boolean): Seq[Method] = {

    getFunctionDecreasesSpecification(f.name) match {
      case DecreasesSpecification(None, _, _) => // no decreases tuple was defined, hence no proof methods required
        return Nil
      case _ => // decreases tuple is defined, hence proof methods are required
    }

    val requireNestedInfo = containsPredicateInstances(DecreasesSpecification.fromNode(f))
    DecreasesSpecification.fromNode(f).productIterator

    val proofMethods: Seq[Method] = {
      if (f.body.nonEmpty) {
        // method proving termination of the functions body.
        val proofMethodName = uniqueName(f.name + "_termination_proof")

        val context = FContext(f)

        val proofMethodBody: Stmt = {
          val stmt: Stmt = Simplifier.simplify(transformExp(f.body.get, context, false))
          if (requireNestedInfo) {
            addNestedPredicateInformation.execute(stmt)
          } else {
            stmt
          }
        }

        if (proofMethodBody != EmptyStmt) {

          val proofMethod = Method(proofMethodName, f.formalArgs, Nil, f.pres, Nil,
            Option(Seqn(Seq(proofMethodBody), Nil)()))(info = f.info)

          Seq(proofMethod)
        } else {
          Nil
        }
      } else Nil
    } ++ {
      if (f.posts.nonEmpty) {
        // method proving termination of postconditions.
        val proofMethodName = uniqueName(f.name + "_posts_termination_proof")
        val context = FContext(f)

        val resultVariable = LocalVarDecl(resultVariableName, f.typ)(f.result.pos, f.result.info, NodeTrafo(f.result))

        // replace all Result nodes with the result variable.
        // and concatenate all posts
        val posts: Exp = f.posts
          .map(p => ViperStrategy.Slim({
            case Result(_) => resultVariable.localVar
          }, Traverse.BottomUp).execute[Exp](p))
          .reduce((e, p) => And(e, p)(e.pos))

        val proofMethodBody: Stmt = {
          val stmt: Stmt = Simplifier.simplify(transformExp(posts, context, false))
          if (requireNestedInfo) {
            addNestedPredicateInformation.execute(stmt)
          } else {
            stmt
          }
        }

        if (proofMethodBody != EmptyStmt) {
          val proofMethod = Method(proofMethodName, f.formalArgs, Nil, f.pres, Nil,
            Option(Seqn(Seq(proofMethodBody), Seq(resultVariable, context.conditionInEx.get))()))(info = f.info)

          Seq(proofMethod)
        } else {
          Nil
        }
      } else Nil
    } ++ {
      if (f.pres.nonEmpty) {
        val proofMethodName = uniqueName(f.name + "_pres_termination_proof")
        val context = FContext(f)

        // concatenate all pres
        val pres = f.pres.reduce((e, p) => And(e, p)(e.pos))

        val proofMethodBody: Stmt = Simplifier.simplify(transformExp(pres, context, true))

        if (proofMethodBody != EmptyStmt) {
          val proofMethod = Method(proofMethodName, f.formalArgs, Nil, Nil, Nil,
            Option(Seqn(Seq(proofMethodBody), Seq(context.conditionInEx.get))()))(info = f.info)

          Seq(proofMethod)
        } else {
          Nil
        }
      } else Nil
    }
    if (respectFuncPermAmounts)
      proofMethods
    else
      proofMethods.map(removeConcretePermissionAmounts)
  }

  /**
    * Given a method, removes all concrete permission amounts and replaces them with wildcard if they are positive,
    * otherwise with none.
    * The transformation is only defined for language constructs that are expected to occur in methods generated
    * to check function termination, i.e., it assumes there are no fold statements, no method calls, no permission
    * introspection etc. It would be unsound in the presence of permission introspection, and possibly incomplete
    * in the presence of method calls etc.
    */
  def removeConcretePermissionAmounts[N <: Node](n: N): N = n.transform({
    case u@Unfold(pap@PredicateAccessPredicate(loc, _)) =>
      // Assume the permission amount is strictly positive; if not, there will be a verification error anyway.
      Unfold(PredicateAccessPredicate(loc, Some(WildcardPerm()()))(pap.pos, pap.info, pap.errT))(u.pos, u.info, u.errT)
    case u@Unfolding(pap@PredicateAccessPredicate(loc, _), b) =>
      Unfolding(PredicateAccessPredicate(loc, Some(WildcardPerm()()))(pap.pos, pap.info, pap.errT), b)(u.pos, u.info, u.errT)
    case pap@PredicateAccessPredicate(loc, op) if !op.exists(_.isInstanceOf[WildcardPerm]) =>
      val papWc = PredicateAccessPredicate(loc, Some(WildcardPerm()()))(pap.pos, pap.info, pap.errT)
      op match {
        case None => papWc
        case Some(p) =>
          // Condition under which the amount is strictly positive; transform wildcard to write because wildcard
          // must not be used outside acc(...) and since arithmetic involving wildcards is forbidden, any positive amount
          // should behave exactly like wildcard.
          val condition: Exp = Simplifier.simplify(PermLtCmp(NoPerm()(), p.transform{case WildcardPerm() => FullPerm()()})())
          condition match {
            case TrueLit() => papWc
            case FalseLit() => TrueLit()()
            case _ => Implies(condition, papWc)(pap.pos, pap.info, pap.errT)
          }
      }
    case fap@FieldAccessPredicate(loc, op) if !op.exists(_.isInstanceOf[WildcardPerm]) =>
      val fapWc = FieldAccessPredicate(loc, Some(WildcardPerm()()))(fap.pos, fap.info, fap.errT)
      op match {
        case None => fapWc
        case Some(p) =>
          val condition: Exp = Simplifier.simplify(PermLtCmp(NoPerm()(), p.transform{case WildcardPerm() => FullPerm()()})())
          condition match {
            case TrueLit() => fapWc
            case FalseLit() => TrueLit()()
            case _ => Implies(condition, fapWc)(fap.pos, fap.info, fap.errT)
          }
      }
    case qp@SourceQuantifiedPermissionAssertion(_, Implies(lhs, rhs)) =>
      // Handle this case explicitly to preserve QP format expected in the AST.
      // If we do not do this, we could get QP assertions like
      // forall vars :: lhs ==> (none < p == acc(loc, p))
      // which the backends cannot handle. So we merge the implications into
      // forall vars :: lhs && none < p ==> acc(loc, p)
      val rhsTransformed = removeConcretePermissionAmounts(rhs)
      rhsTransformed match {
        case i@Implies(newLhs, newRhs) =>
          val completeLhs = And(lhs, newLhs)(lhs.pos, lhs.info, lhs.errT)
          val completeImplies = Implies(completeLhs, newRhs)(i.pos, i.info, i.errT)
          qp.copy(exp = completeImplies)(qp.pos, qp.info, qp.errT)
        case r =>
          val completeImplies = Implies(lhs, rhsTransformed)(r.pos, r.info, r.errT)
          qp.copy(exp = completeImplies)(qp.pos, qp.info, qp.errT)
      }
  }, Traverse.TopDown)


  /**
   * Adds case FuncApp
   * Checks if the termination measure decreases in every function call (to a possibly
   * recursive call)
   *
   * @return a statement representing the expression
   */
  override def transformExp(e: Exp, c: ExpressionContext, inhaleExp: Boolean): Stmt = (e, c) match {
    case (functionCall: FuncApp, context: FunctionContext @unchecked) =>
      val stmts = collection.mutable.ArrayBuffer[Stmt]()

      // check the arguments
      val termChecksOfArgs: Seq[Stmt] = functionCall.getArgs map (a => transformExp(a, context, false))
      stmts.appendAll(termChecksOfArgs)

      getFunctionDecreasesSpecification(context.functionName).tuple match {
        case Some(callerTuple) =>
          val callee = program.findFunction(functionCall.funcname)
          val calleeArgs = functionCall.getArgs

          // map of parameters in the called function to parameters in the current functions (for substitution)
          val mapFormalArgsToCalledArgs = Map(callee.formalArgs.map(_.localVar).zip(calleeArgs): _*)
          val calleeDec = getFunctionDecreasesSpecification(callee.name)

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
            val oldTupleCondition = callerTuple.condition map(Old(_)())

            val oldTupleExpressions = callerTuple.tupleExpressions.map(Old(_)())

            val checks = calleeDec.tuple match {
              case Some(calleeTuple) =>
                // reason would be the callee's defined tuple
                val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(calleeTuple)

                val conditionAssertion = createConditionCheck(oldTupleCondition,
                  calleeTuple.condition.map(_.replace(mapFormalArgsToCalledArgs)), errTrafo, reTrafo)

                val tupleAssertion =
                  createTupleCheck(oldTupleCondition, oldTupleExpressions,
                    calleeTuple.tupleExpressions.map(_.replace(mapFormalArgsToCalledArgs)),
                    errTrafo, reasonTrafoFactory)

                Seq(conditionAssertion, tupleAssertion)
              case None =>
                // reason would be the callee's definition
                val reTrafo = reasonTrafoFactory.generateTupleConditionFalse(callee)
                Seq(createConditionCheck(oldTupleCondition, Some(FalseLit()()), errTrafo, reTrafo))
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

            val oldTupleCondition = callerTuple.condition map(Old(_)())
            val assertion = createConditionCheck(oldTupleCondition,
              Some(calleeDec.getTerminationCondition.replace(mapFormalArgsToCalledArgs)),
              errTrafo, reTrafo)

            stmts.append(assertion)
          }

        case None =>
        // no tuple is defined, hence, nothing must be checked
        // should not happen
      }
      Seqn(stmts.toSeq, Nil)()
    case _ => super.transformExp(e, c, inhaleExp)
  }

  // context creator
  private case class FContext(override val function: Function) extends FunctionContext {
    override val conditionInEx: Option[LocalVarDecl] = Some(LocalVarDecl(condInExVariableName, Bool)())
    override val functionName: String = function.name
    override val mutuallyRecursiveFuncs: Set[Function] = mutuallyRecursiveFunctions.find(_.contains(function)).get
  }

  // context used to create proof method
  private trait FunctionContext extends ExpressionContext {
    val function: Function
    val functionName: String

    val mutuallyRecursiveFuncs: Set[Function]
  }


  private lazy val mutuallyRecursiveFunctions: Seq[Set[Function]] = CallGraph.mutuallyRecursiveVertices(functionCallGraph)

  private lazy val functionCallGraph: DefaultDirectedGraph[Function, DefaultEdge] = {
    val graph = new DefaultDirectedGraph[Function, DefaultEdge](classOf[DefaultEdge])

    program.functions.foreach(graph.addVertex)

    def process(f: Function, n: Node): Unit = {
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