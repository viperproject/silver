// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning.analysis

import viper.silver.ast.utility.Expressions
import viper.silver.ast.{AccessPredicate, Apply, Assert, Assume, BinExp, CurrentPerm, Declaration, DomainFuncApp, Exhale, Exp, FieldAccess, FieldAssign, Fold, ForPerm, FuncApp, Goto, If, Info, Inhale, Label, LocalVar, LocalVarAssign, LocalVarDecl, Method, MethodCall, NoPosition, Package, Position, Program, Quasihavoc, Quasihavocall, Scope, Seqn, Stmt, UnExp, Unfold, While}
import viper.silver.plugin.standard.reasoning.analysis.AnalysisUtils.{AssumeInfluenceSink, AssumeMethodInfluenceSink, AssumeStmtInfluenceSink, AssumeWhileInfluenceSink, HeapSink, HeapSource, InfluenceSink, InfluenceSource, LocalVarSink, LocalVarSource, NonAssumeInfluenceSink, getLocalVarDeclFromLocalVar, getSinkFromVarDecl, getSourceFromVarDecl}
import viper.silver.plugin.standard.reasoning.{Assumes, AssumesNothing, ExistentialElim, FlowAnnotation, FlowVar, FlowVarOrHeap, Heap, InfluencedBy, OldCall, UniversalIntro, Var}
import viper.silver.plugin.standard.termination.{DecreasesClause, DecreasesSpecification, DecreasesTuple, DecreasesWildcard}
import viper.silver.verifier.{AbstractError, ConsistencyError}

import scala.collection.mutable

object AnalysisUtils {
  trait InfluenceSource extends Declaration

  case object HeapSource extends InfluenceSource {
    override def name: String = ".heap"
    override def pos: Position = NoPosition
  }

  /** This is either a local variable or a method's input parameter */
  case class LocalVarSource(v: LocalVar) extends InfluenceSource {
    override def name: String = v.name

    override def pos: Position = v.pos
  }

  def getSourceFromFlowVar(f: FlowVarOrHeap): InfluenceSource = f match {
    case v: Var => LocalVarSource(v.decl)
    case _: Heap => HeapSource
  }

  def getSourceFromVarDecl(v: LocalVarDecl): InfluenceSource = LocalVarSource(v.localVar)

  /** presence of an InfluenceSink indicates that assume stmts are potentially (transitively) present.This sink might
    * map to an emtpy set of sources in case these assume stmts are not influenced by any variables. Note that we use
    * the absence of these sinks in the GraphMap to indicate that no assume stmts are (transitively) present.
    */
  trait InfluenceSink extends Declaration

  trait AssumeInfluenceSink extends InfluenceSink {
    override def name: String = ".assume"
    def pretty: String
  }

  /** Declaration that method might contain assume stmts, which is used for the analysis of the callers of this method */
  case class AssumeMethodInfluenceSink(m: Method) extends AssumeInfluenceSink {
    lazy val pretty = s"Method called at $pos"
    override def pos: Position = m.pos
  }
  /** Declaration that the while loop behaves like an assume stmt, which is used for the analysis of the surrounding method */
  case class AssumeWhileInfluenceSink(w: While) extends AssumeInfluenceSink {
    lazy val pretty = s"Loop at $pos"
    override def pos: Position = w.pos
  }
  /** Declaration that there's an assume or inhale stmt at `pos`, which is used for the analysis of the surrounding method */
  case class AssumeStmtInfluenceSink(i: Inhale) extends AssumeInfluenceSink {
    lazy val pretty = s"Assume or inhale at $pos"
    override def pos: Position = i.pos
  }

  trait NonAssumeInfluenceSink extends InfluenceSink

  case object HeapSink extends NonAssumeInfluenceSink {
    override def name: String = ".heap"
    override def pos: Position = NoPosition
  }

  /** This is either a local variable or a method's output parameter */
  case class LocalVarSink(v: LocalVar) extends NonAssumeInfluenceSink {
    override def name: String = v.name
    override def pos: Position = v.pos
  }

  def getSinkFromFlowVar(f: FlowVar, m: Method): InfluenceSink = f match {
    case f: FlowVarOrHeap => f match {
      case v: Var => LocalVarSink(v.decl)
      case _: Heap => HeapSink
    }
    case _: Assumes => AssumeMethodInfluenceSink(m)
  }

  def getSinkFromVarDecl(v: LocalVarDecl): InfluenceSink = LocalVarSink(v.localVar)

  def isAssumeSink(sink: InfluenceSink): Boolean = sink match {
    case _: AssumeInfluenceSink => true
    case _: NonAssumeInfluenceSink => false
  }

  def getLocalVarDeclFromLocalVar(l: LocalVar): LocalVarDecl = {
    LocalVarDecl(l.name, l.typ)()
  }

  case class TerminationSpecState(guaranteesTermination: Boolean, noTerminationSpec: Boolean)

  private def specifiesTermination(spec: Seq[Exp], info: Info): TerminationSpecState = {
    // we do not analyze whether the conditions cover all cases but are conservative.
    val noTerminationSpec = spec.forall {
      case _: DecreasesClause => false
      case _ => true
    }

    val allInfos = info.getAllInfos[Info]
    val noTerminationInfo = allInfos.forall {
      case _: DecreasesSpecification => false
      case _ => true
    }

    def specifiesCompleteTermination(e: Exp): Boolean = e match {
      case DecreasesTuple(_, None) => true
      case DecreasesWildcard(None) => true
      case _ => false
    }

    val isTerminationSpecComplete = spec.exists(specifiesCompleteTermination)

    val isTerminationInfoComplete = allInfos.exists {
      case DecreasesSpecification(optTuple, optWildcard, _) =>
        optTuple.exists(specifiesCompleteTermination) || optWildcard.exists(specifiesCompleteTermination)
      case _ => false
    }

    TerminationSpecState(
      guaranteesTermination = isTerminationSpecComplete || isTerminationInfoComplete,
      noTerminationSpec = noTerminationSpec && noTerminationInfo
    )
  }

  def specifiesTermination(m: Method): TerminationSpecState = specifiesTermination(m.pres ++ m.posts, m.info)
  def specifiesTermination(w: While): TerminationSpecState = specifiesTermination(w.invs, w.info)
}

case class VarAnalysisGraphMap(prog: Program,
                               logger: ch.qos.logback.classic.Logger,
                               reportErrorWithMsg: AbstractError => Unit) {

  // Maps all influences for a given variable
  private type GraphMap = Map[InfluenceSink, Set[InfluenceSource]]

  // Storage for method analysis
  private val methodAnalysisMap: mutable.Map[Method, GraphMap] = mutable.Map()
  private val methodAnalysisStarted: mutable.ListBuffer[Method] = mutable.ListBuffer()


  def checkUserProvidedInfluencesSpec(): Unit = {
    val methodsWithFlowAnnotations = prog.methods.filter(_.posts.exists {
      case _: FlowAnnotation => true
      case _ => false
    })
    methodsWithFlowAnnotations.foreach(executeTaintedGraphMethodAnalysis)
  }

  /** execute the information flow analysis with graphs.
   * When executed on the universal introduction statement the tainted variables are simply the quantified variables */
  def executeTaintedGraphAnalysis(allVars: Set[LocalVarDecl], tainted: Set[LocalVarDecl], blk: Seqn, volatileSinks: Set[NonAssumeInfluenceSink], u: UniversalIntro): Unit = {
    // Build initial graph where every variable and the heap influences itself
    val initialGraph: GraphMap = allVars.map(k => getSinkFromVarDecl(k) -> Set[InfluenceSource](LocalVarSource(k.localVar))).toMap + (AnalysisUtils.HeapSink -> Set[InfluenceSource](AnalysisUtils.HeapSource))
    val graph = computeInfluenceMap(blk, initialGraph)
    val taintedSources: Set[InfluenceSource] = tainted.map(decl => LocalVarSource(decl.localVar))
    val taintedNonAssumeSinks = volatileSinks.filter(v => graph(v).intersect(taintedSources).nonEmpty)
    taintedNonAssumeSinks.foreach {
      case AnalysisUtils.HeapSink => reportErrorWithMsg(ConsistencyError("Universally introduced variables might influence the heap", u.pos))
      case LocalVarSink(v) => reportErrorWithMsg(ConsistencyError(s"Universally introduced variables might influence variable $v", u.pos))
    }

    val assumeSinks = graph.keySet.collect { case s: AssumeInfluenceSink => s }
    val taintedAssumes = assumeSinks.filter(assumeSink => graph(assumeSink).intersect(taintedSources).nonEmpty)
    taintedAssumes.foreach {
      case AssumeMethodInfluenceSink(p) => reportErrorWithMsg(ConsistencyError(s"Universal introduction variable might influence the method's termination or assume statements in the method's body", p.pos))
      case AssumeStmtInfluenceSink(p) => reportErrorWithMsg(ConsistencyError(s"Universal introduction variable might influence assume statement", p.pos))
      case AssumeWhileInfluenceSink(p) => reportErrorWithMsg(ConsistencyError(s"Universal introduction variable might influence loop termination", p.pos))
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
    if (methodAnalysisStarted.contains(method)) {
      // Case for recursive methods
      if (!methodReturnInfluencesFullySpecified(method)) {
        logger.info(s"Taint analysis encountered an incomplete flow annotation and conservatively over-approximates information flows. (${method.name} ${method.pos})")
      }
      methodAnalysisMap.put(method, getGraphForRecursiveOrAbstractMethod(method))
    } else {
      method.body match {
        case None =>
          // Case for abstract methods
          val map = getGraphForRecursiveOrAbstractMethod(method)
          methodAnalysisMap.put(method, map)
        case Some(seqn) =>
          // Default case
          methodAnalysisStarted.addOne(method)
          val initialGraph: GraphMap =
            method.formalArgs.map(k => getSinkFromVarDecl(k) -> Set(getSourceFromVarDecl(k))).toMap ++
            method.formalReturns.map(k => getSinkFromVarDecl(k) -> Set.empty[InfluenceSource]).toMap +
            (HeapSink -> Set(HeapSource))

          val stmt = seqn.copy(scopedSeqnDeclarations = seqn.scopedSeqnDeclarations.filter({
            case l: LocalVarDecl => !initialGraph.contains(LocalVarSink(l.localVar))
            case _ => true
          }))(seqn.pos, seqn.info, seqn.errT)

          var map = computeInfluenceMap(stmt, initialGraph)
          val assumeVars = map.keySet.collect {
            case v: AssumeInfluenceSink => v
          }

          // Remove all assume nodes and save them as a single assume node for the whole method
          if (assumeVars.nonEmpty) {
            map = map.removedAll(assumeVars) + (AssumeMethodInfluenceSink(method) -> assumeVars.flatMap(v => map(v)))

            // we enter this branch if there are any assume statements in this method's or any callees' body
            // check that user-provided spec did not specify that there are none
            val assumesNothings = method.posts.collect { case n: AssumesNothing => n }
            assumesNothings.foreach {
              n => reportErrorWithMsg(ConsistencyError(s"Contradicting flow annotation: Method might assume or inhale, which is caused by ${assumeVars.map(_.pretty).mkString(", ")}", n.pos))
            }
          }
        
          // Remove sources corresponding to local variables (as opposed to parameters) such that only sources concerned with method arguments and the heap remain:
          val formalVars = method.formalArgs.map(_.localVar)
          map = map.map {
            case (sink, sources) => sink -> sources.filter {
              case LocalVarSource(v) => formalVars.contains(v)
              case _ => true
            }
          }

          // Check calculated value against the provided influencedBy annotations if there are any
          val influencedBys = method.posts.collect { case f: InfluencedBy => f }
          influencedBys.foreach(f => {
            val returnVar = AnalysisUtils.getSinkFromFlowVar(f.v, method)
            val specifiedInfluences = f.varList.map(v => AnalysisUtils.getSourceFromFlowVar(v)).toSet
            val calculatedInfluences = lookupVar(returnVar, map)

            if (!calculatedInfluences.subsetOf(specifiedInfluences)) {
              reportErrorWithMsg(ConsistencyError(s"Specified influence on return variable $returnVar is missing some potential influences. Specified: $specifiedInfluences Calculated: $calculatedInfluences", f.pos))
            }

            if (calculatedInfluences.intersect(specifiedInfluences).size < calculatedInfluences.size) {
              logger.warn(s"Specified influence on return variable $returnVar potentially assumes too many influences. Specified: $specifiedInfluences Calculated: $calculatedInfluences, (${f.pos})")
            }

            map = map + (returnVar -> specifiedInfluences)
          })
          methodAnalysisMap.put(method, map)
      }
    }

    methodAnalysisStarted -= method
  }

  private def methodReturnInfluencesFullySpecified(method: Method): Boolean = {
    val allVars = method.posts.collect({ case f: InfluencedBy => f.v })
    val vars = allVars.collect({ case Var(localVar) => getLocalVarDeclFromLocalVar(localVar)})
    method.formalReturns.forall(v => vars.contains(v)) && allVars.exists(v => v.isInstanceOf[Heap]) && allVars.exists(v => v.isInstanceOf[Assumes])
  }

  /**
    * Returns the graph map for invocations of a recursive or abstract method.
    * In the case of a recursive method, the returned graph map is used as a summary of the recursive call and the caller's
    * analysis continues. The returned graph contains all user-provided influenced-by annotations, which means that the
    * caller's analysis checks that these annotations form a (over-approximating) fixed point. All return variables (and
    * the heap) for which the user did _not_ provide influenced-by annotations, we over-approximate and treat them as
    * being influenced by all input parameters and the heap.
    * While the graph for an abstract method is computed in the very same way, the user-provided annotations is effectively
    * trusted because we cannot use the method's body to check that these annotations represent a valid fixed point.
    * AssumeNothing and "influence assume by" annotations are treated in a similar way, i.e., are included in the returned
    * graph map if specified. If both of these annotations are missing, we over-approximate for possibly non-terminating
    * methods, i.e., the returned graph map specifies that assumes are (potentially) influenced by all input parameters
    * and the heap. If a method is guaranteed to terminate (according to its termination measures), we treat the method
    * as if `AssumeNothing` has been specified.
    */
  private def getGraphForRecursiveOrAbstractMethod(method: Method): GraphMap = {
    // We ignore the assume vertex on purpose here, as a missing assume vertex is treated as if no assume statement appears in the method
    val retSet: Set[InfluenceSink] = method.formalReturns.map(decl => LocalVarSink(decl.localVar)).toSet + HeapSink
    val allMethodArgsSet: Set[InfluenceSource] = method.formalArgs.map(decl => LocalVarSource(decl.localVar)).toSet + HeapSource

    val annotatedInfluencedBys = method.posts.collect({ case a: InfluencedBy => a }).map(a => {
      AnalysisUtils.getSinkFromFlowVar(a.v, method) -> a.varList.map(f => AnalysisUtils.getSourceFromFlowVar(f)).toSet
    }).toMap
    /** influence all return variables, not mentioned by annotation, by every method argument */
    val unannotatedInfluencedBys = (retSet -- annotatedInfluencedBys.keySet).map(retVar => {
      retVar -> allMethodArgsSet
    }).toMap
    val terminates = AnalysisUtils.specifiesTermination(method).guaranteesTermination
    val noAssumes = method.posts.exists {
      case _: AssumesNothing => true
      case _ => false
    }

    // add information about assume statements. We distinguish two cases: (1) Either the user specified which variables
    // influence an assume, that no assume statement occurs or the method terminates and (2) otherwise.
    // In the first case, we do not have to add any influenced by annotations and in the second case, we over-approximate and
    // add an annotation stating that all input parameters and the heap possibly influence a possibly existing assume statements.
    if(annotatedInfluencedBys.contains(AssumeMethodInfluenceSink(method)) || terminates || noAssumes) {
      annotatedInfluencedBys ++ unannotatedInfluencedBys
    } else {
      val assumeInfluence: GraphMap = Map(AssumeMethodInfluenceSink(method) -> allMethodArgsSet)
      annotatedInfluencedBys ++ unannotatedInfluencedBys ++ assumeInfluence
    }
  }

  private def computeInfluenceMap(stmt: Stmt, graphMap: GraphMap): GraphMap = {
    /** extends heap influences by all sources of `exp` and returns the updated graph */
    def addExpSourcesToHeap(graphMap: GraphMap, exp: Exp): GraphMap = {
      val vars = getResolvedVarsFromExp(exp, graphMap)
      graphMap + (HeapSink -> (lookupVar(HeapSink, graphMap) ++ vars))
    }

    stmt match {
      case s: Scope =>
        // Temporarily add the scoped declarations to the graph and remove them afterwards
        val declarations = s.scopedDecls.collect({ case l: LocalVarDecl => l })
        val scopedGraph = graphMap ++ declarations.map(decl => LocalVarSink(decl.localVar) -> Set[InfluenceSource](LocalVarSource(decl.localVar))).toMap
        val graph: GraphMap = s match {
          case Seqn(ss, _) =>
            ss.foldLeft(scopedGraph) { (graph, subStmt) => computeInfluenceMap(subStmt, graph) }
          case u: UniversalIntro => computeInfluenceMap(u.block, scopedGraph)
          case o: OldCall =>
            val met = prog.findMethod(o.methodName)
            computeMethodInfluenceMap(graphMap, met, o.args, o.rets)
          // The quantified variables of the Quasihavocall statement are ignored because they are untainted by definition
          case Quasihavocall(_, lhs, _) =>
            val vars = lhs.map(e => getResolvedVarsFromExp(e, graphMap)).getOrElse(Set.empty)
            graphMap + (HeapSink -> (lookupVar(HeapSink, graphMap) ++ vars))
        }
        graph.removedAll(declarations.map(decl => LocalVarSink(decl.localVar)))
      case LocalVarAssign(lhs, rhs) =>
        val influences = getResolvedVarsFromExp(rhs, graphMap)
        graphMap + (LocalVarSink(lhs) -> influences)
      case If(cond, thn, els) =>
        val conditionVars = getResolvedVarsFromExp(cond, graphMap)
        // For the condition influences, we only care for variables that are declared outside of the if block and for assume annotations
        val writesInIfBlocks = (getModifiedVars(thn) ++ getModifiedVars(els)).filter(v => AnalysisUtils.isAssumeSink(v) || graphMap.contains(v))
        val conditionInfluences = writesInIfBlocks.map(v => v -> (lookupVar(v, graphMap) ++ conditionVars)).toMap

        val thenGraph = computeInfluenceMap(thn, graphMap)
        val elseGraph = computeInfluenceMap(els, graphMap)
        (thenGraph.keySet ++ elseGraph.keySet).map(
          v => v -> (thenGraph.getOrElse(v, Set.empty) ++ elseGraph.getOrElse(v, Set.empty) ++ conditionInfluences.getOrElse(v, Set.empty))
        ).toMap
      case s@ While(cond, _, body) =>
        val unrolledLoop = If(cond, body, Seqn(Seq.empty, Seq.empty)())(body.pos, body.info, body.errT)
        var edgesEqual: Boolean = false
        var mergedGraph = computeInfluenceMap(unrolledLoop, graphMap)
        while (!edgesEqual) {
          val iterationGraph = computeInfluenceMap(unrolledLoop, mergedGraph)
          if(iterationGraph.equals(mergedGraph)) {
            edgesEqual = true
          } else {
            mergedGraph = iterationGraph
          }
        }

        val loopTerminates = AnalysisUtils.specifiesTermination(s).guaranteesTermination
        if(loopTerminates) {
          mergedGraph
        } else {
          mergedGraph + (AssumeWhileInfluenceSink(s) -> getResolvedVarsFromExp(cond, mergedGraph))
        }
      case m: MethodCall =>
        val met = prog.findMethod(m.methodName)
        computeMethodInfluenceMap(graphMap, met, m.args, m.targets)
      case FieldAssign(_, rhs) =>
        // after the assignment, the heap is influenced by everything that influences `rhs` (i.e. `vars`) and all things
        // that influenced the heap before the assignment
        addExpSourcesToHeap(graphMap, rhs)
      case Exhale(exp) =>
        if (exp.isPure) {
          graphMap
        } else {
          addExpSourcesToHeap(graphMap, exp)
        }
      case Fold(acc) =>
        addExpSourcesToHeap(graphMap, acc)
      case Unfold(acc) =>
        addExpSourcesToHeap(graphMap, acc)
      case Apply(exp) =>
        addExpSourcesToHeap(graphMap, exp)
      case Package(wand, _) =>
        addExpSourcesToHeap(graphMap, wand)
      case Quasihavoc(lhs, _) =>
        lhs.map(exp => addExpSourcesToHeap(graphMap, exp)).getOrElse(graphMap)
      case Assert(_) => graphMap
      case Label(_, _) => graphMap
      // Assume analysis
      case a: Inhale =>
        val assumeVars = lookupVar(AssumeStmtInfluenceSink(a), graphMap) ++ getResolvedVarsFromExp(a.exp, graphMap)
        graphMap + (AssumeStmtInfluenceSink(a) -> assumeVars)
      case ExistentialElim(vars, _, exp) => graphMap ++ vars.map(v => LocalVarSink(v.localVar) -> getResolvedVarsFromExp(exp, graphMap))
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
  private def computeMethodInfluenceMap(graphMap: GraphMap, method: Method, callArgs: Seq[Exp], callTargets: Seq[LocalVar]): GraphMap = {
    /** maps formal arguments to the influence sources of the corresponding call arguments */
    val methodArgExpMapping: Map[InfluenceSource, Set[InfluenceSource]] = (method.formalArgs zip callArgs).map {
      case (formalArg, callArg) =>
        getSourceFromVarDecl(formalArg) -> getResolvedVarsFromExp(callArg, graphMap)
    }.toMap + (HeapSource -> lookupVar(HeapSink, graphMap))

    /** maps formal returns, heap, and assume sink to call targets, heap, and assume */
    val retVarMapping: Map[InfluenceSink, InfluenceSink] =
      (method.formalReturns zip callTargets).map {
        case (formalRet, callTarget) => getSinkFromVarDecl(formalRet) -> LocalVarSink(callTarget)
      }.toMap +
      (HeapSink -> HeapSink) +
      // we set the position to the method call instead of the assume statement, so potential error are more readable:
      (AssumeMethodInfluenceSink(method) -> AssumeMethodInfluenceSink(method))

    val resolvedMethodMap = getMethodAnalysisMap(method)
      .filter(v => retVarMapping.contains(v._1))
      .map {
        // extend the method analysis graph by transitivity via the method's arguments:
        case (sink, sources) => retVarMapping(sink) -> sources.flatMap(methodArgExpMapping)
      }

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
  def getModifiedVars(stmt: Stmt): Set[InfluenceSink] = {
    stmt match {
      case Seqn(ss, _) => ss.flatMap(s => getModifiedVars(s)).toSet
      case LocalVarAssign(l, _) => Set(LocalVarSink(l))
      case If(_, thn, els) => getModifiedVars(thn) ++ getModifiedVars(els)
      case While(_, _, body) => getModifiedVars(body)
      case MethodCall(name, _, targets) =>
        val method = prog.methodsByName(name)
        val methodInfluences = getMethodAnalysisMap(method)
        val mightContainAssumeStmts = methodInfluences.keySet.exists(AnalysisUtils.isAssumeSink)
        val targetSinks: Set[InfluenceSink] = targets.map(target => LocalVarSink(target)).toSet
        if (mightContainAssumeStmts) {
          targetSinks + AssumeMethodInfluenceSink(method)
        } else {
          targetSinks
        }
      case i: Inhale => Set(AssumeStmtInfluenceSink(i))
      case _: Assume =>
        assert(assertion = false, "Assume statements should have been replaced by inhale statements")
        ???
      case Label(_, _) => Set.empty
      case Quasihavoc(_, _) => Set(HeapSink)
      case Quasihavocall(_, _, _) => Set(HeapSink)
      case ExistentialElim(vars, _, _) => vars.map(v => LocalVarSink(v.localVar)).toSet
      case _ => Set.empty
    }
  }

  private def lookupVar(variable: InfluenceSink, graphMap: GraphMap): Set[InfluenceSource] = {
    // Assume Nodes are added when they are first encountered(can be a method call or a assume / inhale statement), so they might not exist when looked up
    variable match {
      case _: AssumeInfluenceSink => graphMap.getOrElse(variable, Set.empty)
      case _ =>
        assert(graphMap.contains(variable), "Variable " + variable + " not found in graph analysis")
        graphMap(variable)
    }
  }

  /**
   * Gets all variables used in a given expressions and maps them to their influences specified in given graph map
   */
  private def getResolvedVarsFromExp(exp: Exp, graphMap: GraphMap): Set[InfluenceSource] = {
    getSinksFromExpr(exp).flatMap(v => lookupVar(v, graphMap))
  }

  /** returns all the sinks inside an expression */
  def getSinksFromExpr(exp: Exp): Set[NonAssumeInfluenceSink] = {
    exp match {
      case l: LocalVar => Set(LocalVarSink(l))
      case BinExp(exp1, exp2) => getSinksFromExpr(exp1) ++ getSinksFromExpr(exp2)
      case UnExp(exp) => getSinksFromExpr(exp)
      case f: FuncApp =>
        val isHeapDependent = Expressions.couldBeHeapDependent(f.func(prog), prog)
        // TODO: do we need to filter out Refs?
        f.args.flatMap(e => getSinksFromExpr(e)).toSet ++ (if (isHeapDependent) Set(HeapSink) else Set.empty)
      case DomainFuncApp(_, exps, _) => exps.flatMap(e => getSinksFromExpr(e)).toSet
      case _: ForPerm | _: CurrentPerm => Set(HeapSink)
      case FieldAccess(v, _) => getSinksFromExpr(v) + HeapSink
      case AccessPredicate(access, _) => getSinksFromExpr(access) + HeapSink
      case _ => Set.empty
    }
  }
}
