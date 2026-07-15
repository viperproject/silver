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
      case _: ast.Seqn | _: ast.While | _: ast.If => AssumptionType.Unknown.asDepType()
      case _ => sys.error(s"Dependency type of $stmt is undefined.")
    }
    DependencyTypeInfo(depType)
  }
}

case class DependencyTypeInfo(dependencyType: DependencyType) extends ast.Info {

  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

object JoinType extends Enumeration {
  type JoinType = Value
  val Source, Sink = Value
}

object EdgeType extends Enumeration {
  type EdgeType = Value
  val Up, Down = Value
}

/**
 * Represent the piece of information to be stored in dependency nodes in order to join dependency graphs of
 * individual verification components. Nodes with matching join information are connected by an interprocedural edge.
 */
trait DependencyAnalysisJoinInfo extends ast.Info {
  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false

  def matches(dependencyAnalysisJoinInfo: DependencyAnalysisJoinInfo) : Boolean
}

case class EvalStackDependencyAnalysisJoin(joinType: JoinType, edgeType: EdgeType) extends DependencyAnalysisJoinInfo {
  override def matches(dependencyAnalysisJoinInfo: DependencyAnalysisJoinInfo): Boolean = {
    sys.error("Trying to call matches on an EvalStackDependencyAnalysisJoin.")
  }
}

case class SimpleDependencyAnalysisJoin(sourceInfo: DependencyAnalysisSourceInfo, joinType: JoinType, edgeType: EdgeType) extends DependencyAnalysisJoinInfo {
  override def matches(other: DependencyAnalysisJoinInfo): Boolean = other match {
      case SimpleDependencyAnalysisJoin(sourceInfo1, _, edgeType1) => sourceInfo.equals(sourceInfo1) && edgeType.equals(edgeType1)
      case _ => false
  }
}

/**
 * Represent the piece of information to be stored in dependency nodes in order to finalize the intraprocedural
 * dependency graph. Nodes with matching merge information are connected by an intraprocedural edge.
 */
trait DependencyAnalysisMergeInfo extends ast.Info {

  def isMerge: Boolean

  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

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

trait AdditionalDependencyNodeInfo extends ast.Info {

  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

case class AdditionalAssertionNode() extends AdditionalDependencyNodeInfo

case class AdditionalAssumptionNode() extends AdditionalDependencyNodeInfo
