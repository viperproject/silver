// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning.analysis

import viper.silver.ast.{AccessPredicate, Apply, Assert, Assume, BinExp, CurrentPerm, DomainFuncApp, Exhale, Exp, FieldAccess, FieldAssign, Fold, ForPerm, FuncApp, Goto, If, Inhale, Label, LocalVar, LocalVarAssign, LocalVarDecl, MethodCall, Package, Program, Ref, Seqn, Stmt, UnExp, Unfold, While}
import viper.silver.plugin.standard.reasoning.{ExistentialElim, FlowAnnotation, FlowVar, Heap, OldCall, UniversalIntro, Var}
import viper.silver.verifier.{AbstractError, ConsistencyError}


case class VarAnalysisGraphMap(prog: Program,
                               logger: ch.qos.logback.classic.Logger,
                               reportErrorWithMsg: AbstractError => Unit) {

  val prefix: String = ".init_"
  val heap_vertex: LocalVarDecl = LocalVarDecl(".heap", Ref)()
  private type GraphMap = Map[LocalVarDecl, Set[LocalVarDecl]]


  /** execute the information flow analysis with graphs.
   * When executed on the universal introduction statement the tainted variables are simply the quantified variables */
  def executeTaintedGraphAnalysis(allVars: Set[LocalVarDecl], tainted: Set[LocalVarDecl], blk: Seqn, volatileVars: Set[LocalVarDecl], u: UniversalIntro): Unit = {
    // Build initial graph where every variable and the heap influences itself
    val initialGraph = allVars.map(k => k -> Set(k)).toMap + (heap_vertex -> Set(heap_vertex))

    val graph = computeInfluenceMap(blk, initialGraph, Set(), tainted)
    val problems = volatileVars.filter(v => graph(v).intersect(tainted).nonEmpty)


    if(problems.nonEmpty) {
      reportErrorWithMsg(ConsistencyError("Universal introduction variable might have been assigned to variable " + problems + ", used in the quantified implication", u.pos))
    }
  }

  private def computeInfluenceMap(stmt: Stmt, graphMap: GraphMap, assumeInfluences: Set[LocalVarDecl], tainted: Set[LocalVarDecl]): GraphMap = {
    logger.warn("Statement: " + stmt)
    stmt match {
      // TODO Question: do scopedSeqnDeclarations overwrite existing variables in the subgraphs??
      case Seqn(ss, scopedSeqnDeclarations) =>
        // TODO Question: Idea is, I overwrite all scoped declarations with a variable that only influences itseld
        //      And afterwards restore the influence before the scoped block, is this correct?
        val declarations = scopedSeqnDeclarations.collect({ case l: LocalVarDecl => l })
        val scopedGraph = graphMap ++ declarations.map(decl => decl -> Set(decl)).toMap
        ss.foldLeft(scopedGraph) { (graph, subStmt) => computeInfluenceMap(subStmt, graph, assumeInfluences, tainted) }
      // TODO Question: Havoc?
      // case Havoc(_) => ?
      case LocalVarAssign(lhs, rhs) =>
        val influences = getVarsFromExpr(rhs).flatMap(v => graphMap(v))
        graphMap + (getLocalVarDeclFromLocalVar(lhs) -> influences)
      case UniversalIntro(quantifiedVars, _, _, _, s) => computeInfluenceMap(s, graphMap ++ quantifiedVars.map(v => v -> Set()), assumeInfluences, tainted ++ quantifiedVars)
      case If(cond, thn, els) =>
        val conditionVars = getVarsFromExpr(cond)

        // For the condition influences, we only care for variables that are declared outside of the if block
        val writesInIfBlocks = (getModifiedVars(thn) ++ getModifiedVars(els)).filter(v => graphMap.contains(v));
        val conditionInfluences = writesInIfBlocks.map(v => v -> (graphMap(v) ++ conditionVars.flatMap(c => graphMap(c)))).toMap

        val thn_graph = computeInfluenceMap(thn, graphMap, assumeInfluences ++ conditionVars, tainted)
        val els_graph = computeInfluenceMap(els, graphMap, assumeInfluences ++ conditionVars, tainted)
        thn_graph.keySet.union(els_graph.keySet).map(
          v => v -> (thn_graph.getOrElse(v, Set()) ++ els_graph.getOrElse(v, Set()) ++ conditionInfluences.getOrElse(v, Set()))
        ).toMap
      case While(cond, _, body) =>
        // TODO Question: This seems like quite a smart way to do this, can we keep it this way?
        var iteration_graph = computeInfluenceMap(If(cond, body, Seqn(Seq(), Seq())(body.pos))(body.pos), graphMap, assumeInfluences, tainted)
        var edges_equal: Boolean = false
        var merge_graph = iteration_graph
        var iterations = 1;
        while (!edges_equal) {
          iteration_graph = computeInfluenceMap(If(cond, body, Seqn(Seq(), Seq())(body.pos))(body.pos), merge_graph, assumeInfluences, tainted)
          if(iteration_graph.equals(merge_graph)) {
            edges_equal = true
          } else {
            merge_graph = iteration_graph
          }
          iterations += 1;
        }
        merge_graph
      case MethodCall(methodName, args, targets) =>
        val met = prog.findMethod(methodName)
        computeMethodInfluenceMap(graphMap, args, targets, met.formalArgs, met.formalReturns, met.posts)

      case OldCall(methodName, args, targets, _) =>
        val met = prog.findMethod(methodName)
        computeMethodInfluenceMap(graphMap, args, targets, met.formalArgs, met.formalReturns, met.posts)

      case FieldAssign(_, rhs) =>
        val vars = getVarsFromExpr(rhs)
        graphMap + (heap_vertex -> (graphMap(heap_vertex) ++ vars.filter(v => !v.equals(heap_vertex)).flatMap(v => graphMap(v))))
      case Exhale(exp) =>
        if (exp.isPure) {
          graphMap
        } else {
          val vars = getVarsFromExpr(exp)
          graphMap + (heap_vertex -> (graphMap(heap_vertex) ++ vars))
        }
      case Fold(acc) =>
        val vars = getVarsFromExpr(acc)
        graphMap + (heap_vertex -> (graphMap(heap_vertex) ++ vars))
      case Unfold(acc) =>
        val vars = getVarsFromExpr(acc)
        graphMap + (heap_vertex -> (graphMap(heap_vertex) ++ vars))
      case Apply(exp) =>
        val vars = getVarsFromExpr(exp)
        graphMap + (heap_vertex -> (graphMap(heap_vertex) ++ vars))
      case Package(wand, _) =>
        val vars = getVarsFromExpr(wand)
        graphMap + (heap_vertex -> (graphMap(heap_vertex) ++ vars))


      case a: Inhale =>
        val assumeVars = (assumeInfluences ++ getVarsFromExpr(a.exp)).flatMap(v => graphMap(v) + v).intersect(tainted)
        logger.warn("Assume vars: " + assumeVars)
        if (assumeVars.nonEmpty) {
          reportErrorWithMsg(ConsistencyError(s"Universal introduction variable might influence assume statement: $a ", a.pos))
        }
        graphMap
      case a: Assume =>
        val assumeVars = (assumeInfluences ++ getVarsFromExpr(a.exp)).flatMap(v => graphMap(v) + v).intersect(tainted)
        logger.warn("Assume vars: " + assumeVars)
        if (assumeVars.nonEmpty) {
          reportErrorWithMsg(ConsistencyError(s"Universal introduction variable might influence assume statement: $a ", a.pos))
        }
        graphMap
      case Assert(_) => graphMap
      case Label(_, _) => graphMap
      case e: ExistentialElim =>
        reportErrorWithMsg(ConsistencyError(s"$e is an undefined statement for the modular information flow analysis", e.pos))
        graphMap
      case g: Goto =>
        reportErrorWithMsg(ConsistencyError(s"$g is an undefined statement for the modular information flow analysis", g.pos))
        graphMap
      case _ =>
        reportErrorWithMsg(ConsistencyError(s"$stmt is an undefined statement for the modular information flow analysis", stmt.pos))
        graphMap
    }
  }

  /**
   * returns all the variables inside an expression
   * @param graph existing graph
   * @param exp   expressions from which all variables should be returned
   * @return set of Variable declarations
   */
  def getVarsFromExpr(exp: Exp): Set[LocalVarDecl] = {
    val vars: Set[LocalVarDecl] = Set()
    exp match {
      case l@LocalVar(_, _)   => Set(getLocalVarDeclFromLocalVar(l))
      case BinExp(exp1, exp2) => getVarsFromExpr(exp1) ++ getVarsFromExpr(exp2)
      case UnExp(exp)         => getVarsFromExpr(exp)
      case FuncApp(_, exps) =>
        // TODO Question: how do we differentiate between functions & methods -> functions are side-effect free, so the heap is not needed there
        // TODO Question: Couldn't we use our method influence analysis here as well as an easy way to not over approximate?
        exps.flatMap(e => getVarsFromExpr(e).filter(v => v.typ != Ref)).toSet  // + heap_vertex
      case DomainFuncApp(_, exps, _) =>
        vars ++ exps.flatMap(e => getVarsFromExpr(e))
      case _: ForPerm | _: CurrentPerm =>
          Set(heap_vertex)
      case FieldAccess(v, _) =>
        getVarsFromExpr(v) + heap_vertex
      case AccessPredicate(access, _) =>
        /** Should only be the case in e.g.an inhale or an exhale statement */
        var allVars = vars
        val access_vars = getVarsFromExpr(access)
        access_vars.foreach(v => {
          allVars += v
        })
        allVars
      case _ => Set()
    }
  }

  /**
   * creates an edge between every variable in the expression to every variable that is in scope and returns resulting graph
   */
  private def expInfluencesAllVertices(exp:Exp, graphMap: GraphMap) : GraphMap = {
    // TODO Question: Is this correct? (used by Inhale)
    val vars = getVarsFromExpr(exp)
    val influences = vars.flatMap(v => graphMap(v))
    graphMap.map(f => f._1 -> influences)
  }

  /** creates graph for methodcall and oldcall. maps expressions passed to methods to the method arguments, computes the graph based on the flow annotation,
   * and finally maps the return variables to the variables that the method is assigned to. */
  private def computeMethodInfluenceMap(graphMap: GraphMap, argExpressions: Seq[Exp], retVars: Seq[LocalVar], methodArgVars: Seq[LocalVarDecl], methodRetVars: Seq[LocalVarDecl], posts: Seq[Exp]): GraphMap = {
    /** set of all target variables that have not been included in the influenced by expression up until now */
    val retSet: Set[LocalVarDecl] = methodRetVars.toSet + heap_vertex

    /** create .arg_ declaration for each argument */
    val methodArgExpMapping = (methodArgVars zip argExpressions).map(method_arg => {
      method_arg._1 -> getVarsFromExpr(method_arg._2)
    }).toMap

    val allMethodArgsSet = methodArgExpMapping.values.flatten.toSet + heap_vertex

    val retVarMapping = (retVars.map(l => getLocalVarDeclFromLocalVar(l)) zip methodRetVars)
      .map(vars => vars._2 -> vars._1).toMap + (heap_vertex -> heap_vertex)

    /** Get influences defined in the influenced annotations */
    val annotationInfluences = posts.collect({case FlowAnnotation(returned, arguments) => (returned, arguments)}).map(t => {
      val decl = retVarMapping(getLocalVarDeclFromFlowVar(t._1))
      decl -> (t._2.flatMap(v => methodArgExpMapping(getLocalVarDeclFromFlowVar(v))).toSet ++ graphMap(decl))
    }).toMap

    /** influence all return variables, not mentioned by annotation, by every method argument */
    val otherInfluences = (retSet -- annotationInfluences.keySet).map(retVar => {
      val decl = retVarMapping(retVar)
      decl -> (allMethodArgsSet ++ graphMap(decl))
    })
    val methodInfluences = annotationInfluences ++ otherInfluences

    graphMap ++ methodInfluences
  }

  private def getLocalVarDeclFromFlowVar(f: FlowVar): LocalVarDecl = {
    f match {
      case v: Var => LocalVarDecl(v.decl.name, v.decl.typ)(v.decl.pos)
      case _: Heap => heap_vertex
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
      case MethodCall(_, _, _) => Set()
      case Inhale(_) => Set()
      case Assume(_) => Set()
      case Label(_, _) => Set()
      case _ =>  Set()
    }
  }

  private def getLocalVarDeclFromLocalVar(l: LocalVar): LocalVarDecl = {
    LocalVarDecl(l.name, l.typ)()
  }
}
