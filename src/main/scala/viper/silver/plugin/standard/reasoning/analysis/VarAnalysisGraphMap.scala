// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning.analysis

import viper.silver.ast.utility.Expressions
import viper.silver.ast.{AccessPredicate, Apply, Assert, Assume, BinExp, CurrentPerm, Declaration, DomainFuncApp, Exhale, Exp, FieldAccess, FieldAssign, Fold, ForPerm, FuncApp, Goto, If, Inhale, Label, LocalVar, LocalVarAssign, LocalVarDecl, Method, MethodCall, Package, Position, Program, Quasihavoc, Quasihavocall, Ref, Scope, Seqn, Stmt, UnExp, Unfold, While}
import viper.silver.plugin.standard.reasoning.analysis.AnalysisUtils.{AssumeMethodNode, AssumeNode, AssumeStmtNode, AssumeWhileNode, getLocalVarDeclFromLocalVar, heapVertex}
import viper.silver.plugin.standard.reasoning.{Assumes, ExistentialElim, FlowAnnotation, FlowVar, FlowVarOrHeap, Heap, NoAssumeAnnotation, OldCall, UniversalIntro, Var}
import viper.silver.plugin.standard.termination.{DecreasesSpecification, DecreasesStar, DecreasesTuple, DecreasesWildcard}
import viper.silver.verifier.{AbstractError, ConsistencyError}

import scala.collection.mutable

object AnalysisUtils {
  // TODO add traits for kind of assume sources(e.g assume/inhale stmt, method call, while loop)
  // Position is used for identifying a source for an assume(assume stmt, method call, while loop etc.) and for printing error messages
  trait AssumeNode extends Declaration {
    override def name: String = ".assume"
  }
  case class AssumeMethodNode(pos: Position) extends AssumeNode
  case class AssumeWhileNode(pos: Position) extends AssumeNode
  case class AssumeStmtNode(pos: Position) extends AssumeNode

  val heapVertex: LocalVarDecl = LocalVarDecl(".heap", Ref)()

  def getDeclarationFromFlowVar(f: FlowVar, m: Method): Declaration = {
    f match {
      case v: Var => LocalVarDecl(v.decl.name, v.decl.typ)(v.decl.pos)
      case _: Heap => heapVertex
      case _: Assumes => AssumeMethodNode(m.pos)
    }
  }

  def getLocalVarDeclFromFlowVar(f: FlowVarOrHeap): LocalVarDecl = {
    f match {
      case v: Var => LocalVarDecl(v.decl.name, v.decl.typ)(v.decl.pos)
      case _: Heap => heapVertex
    }
  }

  def getLocalVarDeclFromLocalVar(l: LocalVar): LocalVarDecl = {
    LocalVarDecl(l.name, l.typ)()
  }

  def specifiesTermination(m: Method): (Boolean, Boolean) = {
    val presContain = m.pres.collect({ case DecreasesTuple(_, _) | DecreasesWildcard(_) => true }).nonEmpty
    val postsContain = m.posts.collect({ case DecreasesTuple(_, _) | DecreasesWildcard(_) => true }).nonEmpty

    val presContainStar = m.pres.collect({ case DecreasesStar() => true }).nonEmpty
    val postsContainStar = m.posts.collect({ case DecreasesStar() => true }).nonEmpty


    /** check info for decreases specification */
    val infoContains = m.meta._2 match {
      case _: DecreasesSpecification => true
      case _ => false
    }

    val infoContainsStar = m.meta._2 match {
      case spec: DecreasesSpecification => spec.star.isDefined
      case _ => false
    }

    val containsTerminationMeasure = presContain | postsContain | presContainStar | postsContainStar | infoContains | infoContainsStar
    val mightNotTerminate = !containsTerminationMeasure | presContainStar | postsContainStar | infoContainsStar

    (containsTerminationMeasure, mightNotTerminate)
  }
}

case class VarAnalysisGraphMap(prog: Program,
                               logger: ch.qos.logback.classic.Logger,
                               reportErrorWithMsg: AbstractError => Unit) {

  // Maps all influences for a given variable
  private type GraphMap = Map[Declaration, Set[LocalVarDecl]]

  // Storage for method analysis
  private val methodAnalysisMap: mutable.Map[Method, GraphMap] = mutable.Map()
  private val methodAnalysisStarted: mutable.ListBuffer[Method] = mutable.ListBuffer()


  def checkUserProvidedInfluencesSpec(): Unit = {
    prog.methods.filter(m => m.posts.collect({ case i: FlowAnnotation => i }).nonEmpty).foreach(
      method => executeTaintedGraphMethodAnalysis(method)
    )
  }

  /** execute the information flow analysis with graphs.
   * When executed on the universal introduction statement the tainted variables are simply the quantified variables */
  def executeTaintedGraphAnalysis(allVars: Set[LocalVarDecl], tainted: Set[LocalVarDecl], blk: Seqn, volatileVars: Set[LocalVarDecl], u: UniversalIntro): Unit = {
    // Build initial graph where every variable and the heap influences itself
    val initialGraph = allVars.map(k => k.asInstanceOf[Declaration] -> Set(k)).toMap + (AnalysisUtils.heapVertex -> Set(AnalysisUtils.heapVertex))
    val graph = computeInfluenceMap(blk, initialGraph)
    val problems = volatileVars.filter(v => graph(v).intersect(tainted).nonEmpty)

    if(problems.nonEmpty) {
      reportErrorWithMsg(ConsistencyError("Universal introduction variable might have been assigned to variable " + problems + ", used in the quantified implication", u.pos))
    }

    val assumeProblems = graph.keySet.filter(v => v.isInstanceOf[AssumeNode] && graph(v).intersect(tainted).nonEmpty)
    assumeProblems.foreach {
      case AssumeMethodNode(p) => reportErrorWithMsg(ConsistencyError(s"Universal introduction variable might influence the method's termination or assume statements in the method's body", p))
      case AssumeStmtNode(p) => reportErrorWithMsg(ConsistencyError(s"Universal introduction variable might influence assume statement", p))
      case AssumeWhileNode(p) => reportErrorWithMsg(ConsistencyError(s"Universal introduction variable might influence loop termination", p))
    }
  }

  /**
   * Executes the taint analysis for a method and stores the resulting graph map in methodAnalysisMap and the resulting
   * assume analysis in the methodAssumeAnalysisMap.
   *
   * If a recursive method is encountered, we fall back to the specified influences or a over approximation for the graph map
   * and an over approximation for the assume analysis
   */
  def executeTaintedGraphMethodAnalysis(method: Method): Unit = {
    if (method.body.isEmpty) {
      // Case for abstract methods
      val map = getDefaultMethodInfluences(method)
      methodAnalysisMap.put(method, map)
    } else if(methodAnalysisStarted.contains(method)) {
      // Case for recursive methods
      if(!methodReturnInfluencesFullySpecified(method)) {
        logger.warn(s"Taint analysis does not support recursive method calls. Falling back to specified influences. (${method.name} ${method.pos})")
      }
      methodAnalysisMap.put(method, getDefaultMethodInfluences(method))
    } else {
      // Default case
      methodAnalysisStarted.addOne(method)
      val initialGraph: GraphMap = (method.formalArgs.map(k => k.asInstanceOf[Declaration] -> Set(k)) ++ method.formalReturns.map(k => k -> Set[LocalVarDecl]())).toMap + (AnalysisUtils.heapVertex -> Set(AnalysisUtils.heapVertex))

      val stmt = Seqn(method.body.get.ss, method.body.get.scopedSeqnDeclarations.filter({
        case l: LocalVarDecl => !initialGraph.contains(l)
        case _ => true
      }))(method.body.get.pos, method.body.get.info, method.body.get.errT)

      var map = computeInfluenceMap(stmt, initialGraph)
      val assumeVars = map.keySet.filter(v => v.isInstanceOf[AssumeNode])

      // Remove all assume nodes and save them as a single assume node for the whole method
      if(assumeVars.nonEmpty) {
        map = map.removedAll(assumeVars) + (AssumeMethodNode(method.pos) -> assumeVars.flatMap(v => map(v)))
      }

      // Check calculated value against the provided specification if there are any
      method.posts.collect({ case f: FlowAnnotation => f }).foreach(f => {
        val returnVar = AnalysisUtils.getDeclarationFromFlowVar(f.v, method)
        val specifiedInfluences = f.varList.map(v => AnalysisUtils.getLocalVarDeclFromFlowVar(v)).toSet
        val calculatedInfluences = lookupVar(returnVar, map)

        if (!calculatedInfluences.subsetOf(specifiedInfluences)) {
          reportErrorWithMsg(ConsistencyError(s"Specified influence on return variable $returnVar is missing some potential influences. Specified: $specifiedInfluences Calculated: $calculatedInfluences", f.pos))
        }

        if (calculatedInfluences.intersect(specifiedInfluences).size < calculatedInfluences.size) {
          logger.warn(s"Specified influence on return variable $returnVar potentially assumes too many influences. Specified: $specifiedInfluences Calculated: $calculatedInfluences, (${f.pos})")
        }

        val noAssumesSpecified = method.pres.concat(method.posts).collect({ case _: NoAssumeAnnotation => true }).nonEmpty
        if (noAssumesSpecified && map.contains(AssumeMethodNode(method.pos))) {
          reportErrorWithMsg(ConsistencyError(s"Method with assumesNothing specification might perform an assume or inhale", f.pos))
        }

        map = map + (returnVar -> specifiedInfluences)
      })
      methodAnalysisMap.put(method, map)
    }
    methodAnalysisStarted -= method
  }

  private def methodReturnInfluencesFullySpecified(method: Method): Boolean = {
    val allVars = method.posts.collect({ case f: FlowAnnotation => f.v })
    val vars = allVars.collect({ case Var(localVar) => getLocalVarDeclFromLocalVar(localVar)})
    method.formalReturns.map(v => vars.contains(v)).forall(b => b) && allVars.exists(v => v.isInstanceOf[Heap]) && allVars.exists(v => v.isInstanceOf[Assumes])
  }

  /**
   * Fallback for the influence analysis of methods. If influences for a return variable (including the heap) are declared, they are trusted.
   * Otherwise we over approximate by assuming every method arg (including the heap) influences the return variable.
   */
  private def getDefaultMethodInfluences(method: Method): GraphMap = {
    // We ignore the assume vertex on purpose here, as a missing assume vertex is treated as if no assume statement appears in the method
    val retSet = method.formalReturns.toSet.asInstanceOf[Set[Declaration]] + AnalysisUtils.heapVertex
    val allMethodArgsSet = method.formalArgs.toSet + AnalysisUtils.heapVertex

    val annotationInfluences = method.posts.collect({ case FlowAnnotation(returned, arguments) => (returned, arguments) }).map(t => {
      AnalysisUtils.getDeclarationFromFlowVar(t._1, method) -> t._2.map(f => AnalysisUtils.getLocalVarDeclFromFlowVar(f)).toSet
    }).toMap
    /** influence all return variables, not mentioned by annotation, by every method argument */
    val otherInfluences = (retSet -- annotationInfluences.keySet).map(retVar => {
      retVar -> allMethodArgsSet
    })
    val (containsDecreases, containsDecreasesStar) = AnalysisUtils.specifiesTermination(method)
    val terminates = containsDecreases && !containsDecreasesStar
    val noAssumes = method.pres.concat(method.posts).collect({case _: NoAssumeAnnotation => true}).nonEmpty

    if(annotationInfluences.contains(AssumeMethodNode(method.pos)) || terminates || noAssumes) {
      annotationInfluences ++ otherInfluences
    } else {
      annotationInfluences ++ otherInfluences + (AssumeMethodNode(method.pos) -> allMethodArgsSet)
    }
  }

  private def computeInfluenceMap(stmt: Stmt, graphMap: GraphMap): GraphMap = {
    stmt match {
      case s: Scope =>
        // Temporarily add the scoped declarations to the graph and remove them afterwards
        val declarations = s.scopedDecls.collect({ case l: LocalVarDecl => l })
        val scopedGraph = graphMap ++ declarations.map(decl => decl -> Set(decl)).toMap
        val graph = s match {
          case Seqn(ss, _) =>
            ss.foldLeft(scopedGraph) { (graph, subStmt) => computeInfluenceMap(subStmt, graph) }
          case o: OldCall =>
            val met = prog.findMethod(o.methodName)
            computeMethodInfluenceMap(graphMap, met, o.args, o.rets, o.pos)
          // The quantified variables of the Quasihavocall statement are ignored because they are untainted by definition
          case Quasihavocall(_, lhs, _) =>
            val vars = lhs.map(e => getResolvedVarsFromExp(e, graphMap)).getOrElse(Set())
            graphMap + (AnalysisUtils.heapVertex -> (lookupVar(AnalysisUtils.heapVertex, graphMap) ++ vars))
          case u: UniversalIntro => computeInfluenceMap(u.block, scopedGraph)
        }
        graph.removedAll(declarations)
      case LocalVarAssign(lhs, rhs) =>
        val influences = getResolvedVarsFromExp(rhs, graphMap).flatMap(v => lookupVar(v, graphMap))
        graphMap + (AnalysisUtils.getLocalVarDeclFromLocalVar(lhs) -> influences)
      case If(cond, thn, els) =>
        val conditionVars = getResolvedVarsFromExp(cond, graphMap)
        // For the condition influences, we only care for variables that are declared outside of the if block
        val writesInIfBlocks = (getModifiedVars(thn) ++ getModifiedVars(els)).filter(v => v.isInstanceOf[AssumeNode] || graphMap.contains(v))
        val conditionInfluences = writesInIfBlocks.map(v => v -> (lookupVar(v, graphMap) ++ conditionVars.flatMap(c => lookupVar(c, graphMap)))).toMap

        val thenGraph = computeInfluenceMap(thn, graphMap)
        val elseGraph = computeInfluenceMap(els, graphMap)
        (thenGraph.keySet ++ elseGraph.keySet).map(
          v => v -> (thenGraph.getOrElse(v, Set()) ++ elseGraph.getOrElse(v, Set()) ++ conditionInfluences.getOrElse(v, Set()))
        ).toMap
      case While(cond, invs, body) =>
        var iterationGraph = computeInfluenceMap(If(cond, body, Seqn(Seq(), Seq())(body.pos))(body.pos), graphMap)
        var edgesEqual: Boolean = false
        var mergeGraph = iterationGraph
        while (!edgesEqual) {
          iterationGraph = computeInfluenceMap(If(cond, body, Seqn(Seq(), Seq())(body.pos))(body.pos), mergeGraph)
          if(iterationGraph.equals(mergeGraph)) {
            edgesEqual = true
          } else {
            mergeGraph = iterationGraph
          }
        }

        val loopTerminates = invs.collect { case DecreasesTuple(_, _) | DecreasesWildcard(_) => true }.nonEmpty && invs.collect { case DecreasesStar() => true }.isEmpty
        if(loopTerminates) {
          mergeGraph
        } else {
          mergeGraph + (AssumeWhileNode(cond.pos) -> getResolvedVarsFromExp(cond, mergeGraph))
        }
      case m: MethodCall =>
        val met = prog.findMethod(m.methodName)
        computeMethodInfluenceMap(graphMap, met, m.args, m.targets, m.pos)
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
        val assumeVars = (lookupVar(AssumeStmtNode(a.pos), graphMap) ++ getResolvedVarsFromExp(a.exp, graphMap)).flatMap(v => lookupVar(v, graphMap) + v)
        graphMap + (AssumeStmtNode(a.pos) -> assumeVars)
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
  private def computeMethodInfluenceMap(graphMap: GraphMap, method: Method, callArgs: Seq[Exp], callTargets: Seq[LocalVar], pos: Position): GraphMap = {
    /** set of all target variables that have not been included in the influenced by expression up until now */
    val methodArgExpMapping = (method.formalArgs zip callArgs).map(methodArg =>
      methodArg._1.asInstanceOf[Declaration] -> getResolvedVarsFromExp(methodArg._2, graphMap)
    ).toMap + (AnalysisUtils.heapVertex -> Set(AnalysisUtils.heapVertex))

    val retVarMapping = (callTargets.map(l => AnalysisUtils.getLocalVarDeclFromLocalVar(l)) zip method.formalReturns)
      .map(vars => vars._2.asInstanceOf[Declaration] -> vars._1.asInstanceOf[Declaration]).toMap + (AnalysisUtils.heapVertex -> AnalysisUtils.heapVertex) + (AssumeMethodNode(method.pos) -> AssumeMethodNode(pos))

    val resolvedMethodMap = getMethodAnalysisMap(method)
      .filter(v => retVarMapping.contains(v._1))
      .map(v => retVarMapping(v._1) -> v._2.flatMap(methodArgExpMapping)) +
      (AnalysisUtils.heapVertex -> (graphMap(AnalysisUtils.heapVertex) ++ methodAnalysisMap(method)(AnalysisUtils.heapVertex).flatMap(methodArgExpMapping)))

    // We set the position to the method call instead of the assume statement, so potential error are more readable.
    graphMap ++ resolvedMethodMap
  }

  private def getMethodAnalysisMap(method: Method): GraphMap = {
    if (!methodAnalysisMap.contains(method)) {
      executeTaintedGraphMethodAnalysis(method)
    }

    methodAnalysisMap(method)
  }

  /**
   * get the variables that were modified by the statement stmt
   */
  def getModifiedVars(stmt: Stmt): Set[Declaration] = {
    stmt match {
      case Seqn(ss, _) => ss.flatMap(s => getModifiedVars(s)).toSet
      case LocalVarAssign(l, _) => Set(getLocalVarDeclFromLocalVar(l))
      case If(_, thn, els) => getModifiedVars(thn) ++ getModifiedVars(els)
      case While(_, _, body) => getModifiedVars(body)
      case MethodCall(name, _, targets) =>
        val methodInfluences = getMethodAnalysisMap(prog.methodsByName(name))
        if(methodInfluences.exists(v => v._1.isInstanceOf[AssumeNode])) {
          targets.map(getLocalVarDeclFromLocalVar).toSet + AssumeMethodNode(stmt.pos)
        } else {
          targets.map(getLocalVarDeclFromLocalVar).toSet
        }
      case i: Inhale => Set(AssumeStmtNode(i.pos))
      case a: Assume => Set(AssumeStmtNode(a.pos))
      case Label(_, _) => Set()
      case Quasihavoc(_, _) => Set(heapVertex)
      case Quasihavocall(_, _, _) => Set(heapVertex)
      case ExistentialElim(vars, _, _) => vars.toSet
      case _ => Set()
    }
  }

  private def lookupVar(variable: Declaration, graphMap: GraphMap): Set[LocalVarDecl] = {
    // Assume Nodes are added when they are first encountered(can be a method call or a assume / inhale statement), so they might not exist when looked up
    if(variable.isInstanceOf[AssumeNode]) {
      graphMap.getOrElse(variable, Set())
    } else {
      assert(graphMap.contains(variable), "Variable " + variable + " not found in graph analysis")
      graphMap(variable)
    }
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
