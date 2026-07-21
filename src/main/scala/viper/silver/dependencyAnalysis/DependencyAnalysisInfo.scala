// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silver.dependencyAnalysis

import viper.silver.ast
import viper.silver.dependencyAnalysis.AssumptionType._
import viper.silver.dependencyAnalysis.DependencyType._
import viper.silver.dependencyAnalysis.EdgeType.EdgeType
import viper.silver.dependencyAnalysis.JoinType.JoinType
import viper.silver.plugin.standard.refute.Refute

object DependencyTypeInfo {
  def getDependencyTypeInfo(stmt: ast.Stmt): DependencyTypeInfo = {
    val depType = stmt match {
      case _: ast.MethodCall => MethodCall.asDepType()
      case  _: ast.NewStmt | _: ast.AbstractAssign => SourceCode.asDepType()
      case _: ast.Exhale | _: ast.Assert | _: Refute => ExplicitAssertion
      case _: ast.Inhale | _: ast.Assume => ExplicitAssumption
      case _: ast.Fold | _: ast.Unfold | _: ast.Package | _: ast.Apply => Rewrite.asDepType()
      case _: ast.Quasihavoc | _: ast.Quasihavocall => SourceCode.asDepType()
      case _ => AssumptionType.Unknown.asDepType() // other statements do not introduce assumptions or are composed of statements that we already covered. We can ignore these.
    }
    DependencyTypeInfo(depType)
  }

  def getInternalDepTypeInfo: DependencyTypeInfo = DependencyTypeInfo(DependencyType(AssumptionType.Internal))
}

case class DependencyTypeInfo(dependencyType: DependencyType) extends ast.Info {

  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

object JoinType extends Enumeration {
  type JoinType = Value
  val Source, Sink = Value
}

/**
 * Up = moving up the call graph, e.g. from precondition to all calls to its method
 * Down = moving down the call graph, e.g. from method call to the method's postcondition
 */
object EdgeType extends Enumeration {
  type EdgeType = Value
  val Up, Down = Value
}

/**
 * Represent the piece of information to be stored in dependency nodes in order to join dependency graphs of
 * individual verification components. Nodes with matching join information are connected by an interprocedural edge.
 *
 * For example, method calls and the method's pre/postconditions are joined by attaching join info to the AST nodes accordingly.
 */
trait DependencyAnalysisJoinInfo extends ast.Info {
  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false

  def matches(dependencyAnalysisJoinInfo: DependencyAnalysisJoinInfo) : Boolean
}

/**
 * Temporary placeholder indicating that the source info of this join is determined later on (i.e. by the most specific source info).
 * It should always be transformed to another type of join info before creating a dependency node.
 */
case class EvalStackDependencyAnalysisJoin(joinType: JoinType, edgeType: EdgeType) extends DependencyAnalysisJoinInfo {
  override def matches(dependencyAnalysisJoinInfo: DependencyAnalysisJoinInfo): Boolean = {
    // These join infos should be transformed to SimpleDependencyAnalysisJoin before joining the graphs. Hence, we throw an error if that is not the case.
    sys.error("Trying to call matches on an EvalStackDependencyAnalysisJoin.")
  }
}

/**
 * @param sourceInfo a piece of information used to determine the join edges
 * @param joinType indicates whether the node is the source or sink of the joining edge
 * @param edgeType indicates the type of edge
 *
 * Dependency nodes having join infos with identical source info and edge type are to be connected by an edge.
 */
case class SimpleDependencyAnalysisJoin(sourceInfo: DependencyAnalysisSourceInfo, joinType: JoinType, edgeType: EdgeType) extends DependencyAnalysisJoinInfo {
  override def matches(other: DependencyAnalysisJoinInfo): Boolean = other match {
      case SimpleDependencyAnalysisJoin(sourceInfo1, _, edgeType1) => sourceInfo.equals(sourceInfo1) && edgeType.equals(edgeType1)
      case _ => false
  }
}

/**
 *  The merge infos are one of the main measures to make the analysis more precise. It indicates which edges, that are not already discovered through
 *  UNSAT cores, are added to intra-procedural graphs. All nodes with the same merge info are interconnected, i.e. all its assumption nodes depend on (= have an edge to)
 *  all its assertion nodes.
 *
 *  By default, the merge info is identical to the source info. However, we can control this behavior
 *  by setting custom merge infos. Nodes can have arbitrarily many merge infos, e.g. some nodes have merge info A, some have B,
 *  and some have both thus connecting nodes with only A and B in a controlled manner.
 *
 *  Dependency nodes with NoDependencyAnalysisMerge() are ignored, e.g. no edges to/from them are added during the finalization phase of the intraprocedural graph.
 *  We mainly use it for internal nodes, e.g. infeasibility nodes.
 *
 *  An example usage of custom merge infos can be found for field assignments (DefaultHeapSupportRules.execFieldAssign).
 */
trait DependencyAnalysisMergeInfo extends ast.Info {

  def isMerge: Boolean

  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

/*
  Indicates that no edge should be added.
 */
case class NoDependencyAnalysisMerge() extends DependencyAnalysisMergeInfo {
  override def isMerge: Boolean = false
}

case class SimpleDependencyAnalysisMerge(sourceInfo: DependencyAnalysisSourceInfo) extends DependencyAnalysisMergeInfo {
  override def isMerge: Boolean = true
}

case class CompositeDependencyAnalysisMergeInfo(sourceInfo1: DependencyAnalysisSourceInfo, sourceInfo2: DependencyAnalysisSourceInfo) extends DependencyAnalysisMergeInfo {
  override def isMerge: Boolean = true
}

object DependencyAnalysisMergeInfo {
  def attachExpMergeInfo(exps: Seq[ast.Exp], sourceInfo2: Option[DependencyAnalysisSourceInfo]): Seq[ast.Exp] = {
    exps.map(attachExpMergeInfo(_, sourceInfo2))
  }

  def attachExpMergeInfo(exp: ast.Exp, sourceInfo2: Option[DependencyAnalysisSourceInfo]): ast.Exp = {
    val expSourceInfo = DependencyAnalysisSourceInfo.createAnalysisSourceInfo(exp)
    attachExpMergeInfo(exp, expSourceInfo, sourceInfo2)
  }

  def attachExpMergeInfo(exp: ast.Exp, mergeInfo: DependencyAnalysisMergeInfo): ast.Exp = {
    exp.withMeta((exp.pos, ast.MakeInfoPair(mergeInfo, exp.info), exp.errT))
  }

  def attachExpMergeInfo(exp: ast.Exp, sourceInfo1: DependencyAnalysisSourceInfo, sourceInfo2: Option[DependencyAnalysisSourceInfo]): ast.Exp = {
    val mergeInfo = if(sourceInfo2.isDefined)
      CompositeDependencyAnalysisMergeInfo(sourceInfo1, sourceInfo2.get)
    else
      SimpleDependencyAnalysisMerge(sourceInfo1)
    exp.withMeta((exp.pos, ast.MakeInfoPair(mergeInfo, exp.info), exp.errT))
  }
}

/**
 * Sometimes we need to enforce the creation of assertion or assumption nodes because they might not be created automatically due to encoding details.
 * By attaching an appropriate AdditionalDependencyNodeInfo to the node's info field, the creation of a corresponding node is enforced.
 *
 * For example, upcasts in Gobra require an implementation proof. This proof is encoded as a dedicated method but the connection to the upcast
 * is not apparent in the resulting Viper program. The upcast might not introduce an assertion node at all. In this case, we attach an
 * AdditionalAssertionNode to the Viper node's info field. (We also attach join infos to encode the connection to the implementation proof.)
 */
trait AdditionalDependencyNodeInfo extends ast.Info {

  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

case class AdditionalAssertionNode() extends AdditionalDependencyNodeInfo

case class AdditionalAssumptionNode() extends AdditionalDependencyNodeInfo
