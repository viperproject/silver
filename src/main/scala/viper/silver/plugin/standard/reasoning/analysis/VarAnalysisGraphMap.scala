// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning.analysis

import viper.silver.ast.utility.Expressions
import viper.silver.ast.{AccessPredicate, Apply, Assert, Assume, BinExp, CurrentPerm, DomainFuncApp, Exhale, Exp, FieldAccess, FieldAssign, Fold, ForPerm, FuncApp, Goto, If, Inhale, Label, LocalVar, LocalVarAssign, LocalVarDecl, Method, MethodCall, Package, Position, Program, Quasihavoc, Quasihavocall, Ref, Scope, Seqn, Stmt, UnExp, Unfold, While}
import viper.silver.plugin.standard.reasoning.analysis.AnalysisUtils.{getLocalVarDeclFromLocalVar, heapVertex}
import viper.silver.plugin.standard.reasoning.{ExistentialElim, FlowAnnotation, FlowVar, Heap, OldCall, UniversalIntro, Var}
import viper.silver.verifier.{AbstractError, ConsistencyError}

import scala.collection.mutable

object AnalysisUtils {
  val heapVertex: LocalVarDecl = LocalVarDecl(".heap", Ref)()

  def getLocalVarDeclFromFlowVar(f: FlowVar): LocalVarDecl = {
    f match {
      case v: Var => LocalVarDecl(v.decl.name, v.decl.typ)(v.decl.pos)
      case _: Heap => heapVertex
    }
  }

  /**
   * get the variables that were modified by the statement stmt
   */
  def getModifiedVars(stmt: Stmt): Set[LocalVarDecl] = {
    stmt match {
      case Seqn(ss, _) => ss.flatMap(s => getModifiedVars(s)).toSet
      case LocalVarAssign(l, _) => Set(getLocalVarDeclFromLocalVar(l))
      case If(_, thn, els) => getModifiedVars(thn) ++ getModifiedVars(els)
      case While(_, _, body) => getModifiedVars(body)
      case MethodCall(_, _, targets) => targets.map(getLocalVarDeclFromLocalVar).toSet
      case Inhale(_) => Set()
      case Assume(_) => Set()
      case Label(_, _) => Set()
      case Quasihavoc(_, _) => Set(heapVertex)
      case Quasihavocall(_, _, _) => Set(heapVertex)
      case ExistentialElim(vars, _, _) => vars.toSet
      case _ => Set()
    }
  }

  def getLocalVarDeclFromLocalVar(l: LocalVar): LocalVarDecl = {
    LocalVarDecl(l.name, l.typ)()
  }
}


case class VarAnalysisGraphMap(prog: Program,
                               logger: ch.qos.logback.classic.Logger,
                               reportErrorWithMsg: AbstractError => Unit) {

  // Maps all influences for a given variable
  private type GraphMap = Map[LocalVarDecl, Set[LocalVarDecl]]
  // Maps all influences for a statement at a given position
  private type AssumeAnalysis = mutable.Map[Position, Set[LocalVarDecl]]


  // Storage for method analysis
  private val methodAnalysisMap: mutable.Map[Method, GraphMap] = mutable.Map()
  private val methodAssumeAnalysisMap: mutable.Map[Method, AssumeAnalysis] = mutable.Map()
  private val methodAnalysisStarted: mutable.ListBuffer[Method] = mutable.ListBuffer()


  /** execute the information flow analysis with graphs.
   * When executed on the universal introduction statement the tainted variables are simply the quantified variables */
  def executeTaintedGraphAnalysis(allVars: Set[LocalVarDecl], tainted: Set[LocalVarDecl], blk: Seqn, volatileVars: Set[LocalVarDecl], u: UniversalIntro): Unit = {
    // Build initial graph where every variable and the heap influences itself
    val initialGraph = allVars.map(k => k -> Set(k)).toMap + (AnalysisUtils.heapVertex -> Set(AnalysisUtils.heapVertex))
    val assumeAnalysis: AssumeAnalysis = mutable.Map()
    val graph = computeInfluenceMap(blk, initialGraph, Set())(assumeAnalysis)
    val problems = volatileVars.filter(v => graph(v).intersect(tainted).nonEmpty)

    if(problems.nonEmpty) {
      reportErrorWithMsg(ConsistencyError("Universal introduction variable might have been assigned to variable " + problems + ", used in the quantified implication", u.pos))
    }
    assumeAnalysis.foreach(v => {
      val assumeVars = v._2.intersect(tainted)
      if (assumeVars.nonEmpty) {
        val vars = assumeVars.map(v => s"'${v.name}'").mkString(", ")
        val err = if (assumeVars.size == 1) {
          "variable " + vars
        } else {
          "variables " + vars
        }
        reportErrorWithMsg(ConsistencyError(s"Tainted $err (${u.pos}) might influence assume statement", v._1))
      }
    })
  }

  /**
   * Executes the taint analysis for a method and stores the resulting graph map in methodAnalysisMap and the resulting
   * assume analysis in the methodAssumeAnalysisMap.
   *
   * If a recursive method is encountered, we fall back to the specified influences or a over approximation for the graph map
   * and an over approximation for the assume analysis
   */
  private def executeTaintedGraphMethodAnalysis(method: Method): Unit = {
    if(methodAnalysisStarted.contains(method) || method.body.isEmpty) {
      if(methodAnalysisStarted.contains(method)) {
        logger.warn(s"Taint analysis does not support recursive method calls. Falling back to specified influences. (${method.name} ${method.pos})")
      }
      methodAnalysisMap.put(method, getDefaultMethodInfluences(method))
      methodAssumeAnalysisMap.put(method, overApproximateAssumeInfluences(method))
    } else {
      methodAnalysisStarted.addOne(method)
      val initialGraph: GraphMap = (method.formalArgs.map(k => k -> Set(k)) ++ method.formalReturns.map(k => k -> Set[LocalVarDecl]())).toMap + (AnalysisUtils.heapVertex -> Set(AnalysisUtils.heapVertex))

      val stmt = Seqn(method.body.get.ss, method.body.get.scopedSeqnDeclarations.filter({
        case l: LocalVarDecl => !initialGraph.contains(l)
        case _ => true
      }))(method.body.get.pos, method.body.get.info, method.body.get.errT)

      val assumeAnalysis: AssumeAnalysis = mutable.Map()
      val map = computeInfluenceMap(stmt, initialGraph, Set())(assumeAnalysis)

      if(!methodAnalysisMap.contains(method)) {
        // Check calculated value against the provided specification if there are any
        method.posts.collect({ case f: FlowAnnotation => f }).foreach(f => {
          val returnVar = AnalysisUtils.getLocalVarDeclFromFlowVar(f.v)
          val specifiedInfluences = f.varList.map(AnalysisUtils.getLocalVarDeclFromFlowVar).toSet
          val calculatedInfluences = lookupVar(returnVar, map)
          if (calculatedInfluences != specifiedInfluences) {
            reportErrorWithMsg(ConsistencyError(s"Specified influence on return variable $returnVar differs from calculated value. Specified: $specifiedInfluences Calculated: $calculatedInfluences", f.pos))
          }
        })

        methodAnalysisMap.put(method, map)
        methodAssumeAnalysisMap.put(method, assumeAnalysis)
      }
    }
    methodAnalysisStarted -= method
  }

  /**
   * Fallback for the influence analysis of methods. If influences for a return variable (including the heap) are declared, they are trusted.
   * Otherwise we over approximate by assuming every method arg (including the heap) influences the return variable.
   */
  private def getDefaultMethodInfluences(method: Method): GraphMap = {
    val retSet = method.formalReturns.toSet + AnalysisUtils.heapVertex
    val allMethodArgsSet = method.formalArgs.toSet + AnalysisUtils.heapVertex

    val annotationInfluences = method.posts.collect({ case FlowAnnotation(returned, arguments) => (returned, arguments) }).map(t => {
      AnalysisUtils.getLocalVarDeclFromFlowVar(t._1) -> t._2.map(AnalysisUtils.getLocalVarDeclFromFlowVar).toSet
    }).toMap
    /** influence all return variables, not mentioned by annotation, by every method argument */
    val otherInfluences = (retSet -- annotationInfluences.keySet).map(retVar => {
      retVar -> allMethodArgsSet
    })
    annotationInfluences ++ otherInfluences
  }

  /**
   * Over approximates the assume analysis, by assuming that the method's arguments influence every inhale statement
   * that occurs in this method or in any transitively called method.
   */
  private def overApproximateAssumeInfluences(method: Method): AssumeAnalysis = {
    var allCalledMethods: Set[Method] = Set(method)
    var nextSet: Set[Method] = allCalledMethods ++ getAllCalledMethods(method)

    while (allCalledMethods != nextSet) {
      allCalledMethods = nextSet
      nextSet = allCalledMethods ++ allCalledMethods.flatMap(getAllCalledMethods)
    }

    val allInhales = allCalledMethods.flatMap(met => met.deepCollectInBody({ case a: Inhale => a }))
    val assumeAnalysis: AssumeAnalysis = mutable.Map()
    assumeAnalysis.addAll(allInhales.map(i => i.pos -> method.formalArgs.toSet))
  }

  private def getAllCalledMethods(method: Method): Set[Method] = method.deepCollectInBody({ case a: MethodCall => a }).map(m => prog.findMethod(m.methodName)).toSet

  private def computeInfluenceMap(stmt: Stmt, graphMap: GraphMap, pathInfluencingVariables: Set[LocalVarDecl])(implicit assumeAnalysis: AssumeAnalysis): GraphMap = {
    stmt match {
      case s: Scope =>
        // Temporarily add the scoped declarations to the graph and remove them afterwards
        val declarations = s.scopedDecls.collect({ case l: LocalVarDecl => l })
        val scopedGraph = graphMap ++ declarations.map(decl => decl -> Set(decl)).toMap
        val graph = s match {
          case Seqn(ss, _) =>
            ss.foldLeft(scopedGraph) { (graph, subStmt) => computeInfluenceMap(subStmt, graph, pathInfluencingVariables) }
            // TODO Why is OldCall a Scope statement?
          case o: OldCall =>
            val met = prog.findMethod(o.methodName)
            computeMethodInfluenceMap(graphMap, met, o.args, o.rets, pathInfluencingVariables, o.pos)
          // The quantified variables of the Quasihavocall statement are ignored because they are untainted by definition
          case Quasihavocall(_, lhs, _) =>
            val vars = lhs.map(e => getResolvedVarsFromExp(e, graphMap)).getOrElse(Set())
            graphMap + (AnalysisUtils.heapVertex -> (lookupVar(AnalysisUtils.heapVertex, graphMap) ++ vars))
          case u: UniversalIntro => computeInfluenceMap(u.block, scopedGraph, pathInfluencingVariables)
        }
        graph.removedAll(declarations)
      case LocalVarAssign(lhs, rhs) =>
        val influences = getResolvedVarsFromExp(rhs, graphMap).flatMap(v => lookupVar(v, graphMap))
        graphMap + (AnalysisUtils.getLocalVarDeclFromLocalVar(lhs) -> influences)
      case If(cond, thn, els) =>
        val conditionVars = getResolvedVarsFromExp(cond, graphMap)
        // For the condition influences, we only care for variables that are declared outside of the if block
        val writesInIfBlocks = (AnalysisUtils.getModifiedVars(thn) ++ AnalysisUtils.getModifiedVars(els)).filter(v => graphMap.contains(v))
        val conditionInfluences = writesInIfBlocks.map(v => v -> (lookupVar(v, graphMap) ++ conditionVars.flatMap(c => lookupVar(c, graphMap)))).toMap

        val thenGraph = computeInfluenceMap(thn, graphMap, pathInfluencingVariables ++ conditionVars)
        val elseGraph = computeInfluenceMap(els, graphMap, pathInfluencingVariables ++ conditionVars)
        (thenGraph.keySet ++ elseGraph.keySet).map(
          v => v -> (thenGraph.getOrElse(v, Set()) ++ elseGraph.getOrElse(v, Set()) ++ conditionInfluences.getOrElse(v, Set()))
        ).toMap
      case While(cond, _, body) =>
        var iterationGraph = computeInfluenceMap(If(cond, body, Seqn(Seq(), Seq())(body.pos))(body.pos), graphMap, pathInfluencingVariables)
        var edgesEqual: Boolean = false
        var mergeGraph = iterationGraph
        while (!edgesEqual) {
          iterationGraph = computeInfluenceMap(If(cond, body, Seqn(Seq(), Seq())(body.pos))(body.pos), mergeGraph, pathInfluencingVariables)
          if(iterationGraph.equals(mergeGraph)) {
            edgesEqual = true
          } else {
            mergeGraph = iterationGraph
          }
        }
        mergeGraph
      case m: MethodCall =>
        val met = prog.findMethod(m.methodName)
        computeMethodInfluenceMap(graphMap, met, m.args, m.targets, pathInfluencingVariables, m.pos)
      case FieldAssign(_, rhs) =>
        val vars = getResolvedVarsFromExp(rhs, graphMap)
        graphMap + (AnalysisUtils.heapVertex -> (lookupVar(AnalysisUtils.heapVertex, graphMap) ++ vars.filter(v => !v.equals(AnalysisUtils.heapVertex)).flatMap(v => graphMap(v))))
      case Exhale(exp) =>
        if (exp.isPure) {
          graphMap
        } else {
          val vars = getResolvedVarsFromExp(exp, graphMap)
          graphMap + (AnalysisUtils.heapVertex -> (lookupVar(AnalysisUtils.heapVertex, graphMap) ++ vars))
        }
      case Fold(acc) =>
        val vars = getResolvedVarsFromExp(acc, graphMap)
        graphMap + (AnalysisUtils.heapVertex -> (lookupVar(AnalysisUtils.heapVertex, graphMap) ++ vars))
      case Unfold(acc) =>
        val vars = getResolvedVarsFromExp(acc, graphMap)
        graphMap + (AnalysisUtils.heapVertex -> (lookupVar(AnalysisUtils.heapVertex, graphMap) ++ vars))
      case Apply(exp) =>
        val vars = getResolvedVarsFromExp(exp, graphMap)
        graphMap + (AnalysisUtils.heapVertex -> (lookupVar(AnalysisUtils.heapVertex, graphMap) ++ vars))
      case Package(wand, _) =>
        val vars = getResolvedVarsFromExp(wand, graphMap)
        graphMap + (AnalysisUtils.heapVertex -> (lookupVar(AnalysisUtils.heapVertex, graphMap) ++ vars))
      case Quasihavoc(lhs, _) =>
        val vars = lhs.map(e => getResolvedVarsFromExp(e, graphMap)).getOrElse(Set())
        graphMap + (AnalysisUtils.heapVertex -> (lookupVar(AnalysisUtils.heapVertex, graphMap) ++ vars))
      case Assert(_) => graphMap
      case Label(_, _) => graphMap
      // Assume analysis
      case a: Inhale =>
        val assumeVars = (pathInfluencingVariables ++ getResolvedVarsFromExp(a.exp, graphMap)).flatMap(v => lookupVar(v, graphMap) + v)
        assumeAnalysis.addOne(a.pos -> assumeVars)
        graphMap
      case ExistentialElim(vars, _, exp) => graphMap ++ vars.map(v => v -> getResolvedVarsFromExp(exp, graphMap))
      // Non handled cases
      case a: Assume =>
        reportErrorWithMsg(ConsistencyError("Unexpected assume statement in the modular information flow analysis", a.pos))
        graphMap
      case g: Goto =>
        reportErrorWithMsg(ConsistencyError(s"$g is an undefined statement for the modular information flow analysis", g.pos))
        graphMap
      case _ =>
        reportErrorWithMsg(ConsistencyError(s"$stmt is an undefined statement for the modular information flow analysis", stmt.pos))
        graphMap
    }
  }

  /** creates graph for method call and old call. maps expressions passed to methods to the method arguments, computes the graph based on the flow annotation,
   * and finally maps the return variables to the variables that the method is assigned to. */
  private def computeMethodInfluenceMap(graphMap: GraphMap, method: Method, callArgs: Seq[Exp], callTargets: Seq[LocalVar], pathInfluencingVars: Set[LocalVarDecl], pos: Position)(implicit assumeAnalysis: AssumeAnalysis): GraphMap = {
    /** set of all target variables that have not been included in the influenced by expression up until now */
    val methodArgExpMapping = (method.formalArgs zip callArgs).map(methodArg =>
      methodArg._1 -> getResolvedVarsFromExp(methodArg._2, graphMap)
    ).toMap + (AnalysisUtils.heapVertex -> Set(AnalysisUtils.heapVertex))
    val retVarMapping = (callTargets.map(l => AnalysisUtils.getLocalVarDeclFromLocalVar(l)) zip method.formalReturns)
      .map(vars => vars._2 -> vars._1).toMap + (AnalysisUtils.heapVertex -> AnalysisUtils.heapVertex)

    if(!methodAnalysisMap.contains(method)) {
      executeTaintedGraphMethodAnalysis(method)
    }

    val resolvedMethodMap = methodAnalysisMap(method)
      .filter(v => retVarMapping.contains(v._1))
      .map(v => retVarMapping(v._1) -> v._2.flatMap(methodArgExpMapping)) +
      (AnalysisUtils.heapVertex -> (graphMap(AnalysisUtils.heapVertex) ++ methodAnalysisMap(method)(AnalysisUtils.heapVertex).flatMap(methodArgExpMapping)))

    val methodAssumeAnalysis = methodAssumeAnalysisMap(method)

    // We set the position to the method call instead of the assume statement, so potential error are more readable.
    assumeAnalysis.addAll(methodAssumeAnalysis.map(v => pos -> (v._2.flatMap(v => methodArgExpMapping(v)) ++ pathInfluencingVars)))

    logger.warn("{}", methodAnalysisMap(method))
    logger.warn("{}", retVarMapping)

    logger.warn("{}", resolvedMethodMap)
    graphMap ++ resolvedMethodMap
  }

  private def lookupVar(variable: LocalVarDecl, graphMap: GraphMap): Set[LocalVarDecl] = {
    assert(graphMap.contains(variable), "Variable " + variable + " not found in graph analysis")
    graphMap(variable)
  }

  /**
   * Gets all variables used in a given expressions and maps them to their influences specified in given graph map
   */
  private def getResolvedVarsFromExp(exp: Exp, graphMap: GraphMap): Set[LocalVarDecl] = {
    getLocalVarDeclsFromExpr(exp).flatMap(v => lookupVar(v, graphMap))
  }

  /**
   * returns all the variables inside an expression
   *
   * @param exp expressions from which all variables should be returned
   * @return set of Variable declarations
   */
  def getLocalVarDeclsFromExpr(exp: Exp): Set[LocalVarDecl] = {
    exp match {
      case l@LocalVar(_, _) => Set(getLocalVarDeclFromLocalVar(l))
      case BinExp(exp1, exp2) => getLocalVarDeclsFromExpr(exp1) ++ getLocalVarDeclsFromExpr(exp2)
      case UnExp(exp) => getLocalVarDeclsFromExpr(exp)
      case f: FuncApp =>
        val heapDependent = Expressions.couldBeHeapDependent(f.func(prog), prog)
        f.args.flatMap(e => getLocalVarDeclsFromExpr(e).filter(v => v.typ != Ref)).toSet ++ (if (heapDependent) Set(heapVertex) else Set())
      case DomainFuncApp(_, exps, _) => exps.flatMap(e => getLocalVarDeclsFromExpr(e)).toSet
      case _: ForPerm | _: CurrentPerm => Set(heapVertex)
      case FieldAccess(v, _) => getLocalVarDeclsFromExpr(v) + heapVertex
      case AccessPredicate(access, _) => getLocalVarDeclsFromExpr(access) + heapVertex
      case _ => Set()
    }
  }
}
