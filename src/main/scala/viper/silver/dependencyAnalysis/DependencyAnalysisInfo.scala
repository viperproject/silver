package viper.silver.dependencyAnalysis

import viper.silver.ast
import viper.silver.dependencyAnalysis.DependencyType._
import viper.silver.dependencyAnalysis.EdgeType.EdgeType
import viper.silver.dependencyAnalysis.JoinType.JoinType

object DependencyTypeInfo {
	def getDependencyTypeInfo(stmt: ast.Stmt): DependencyTypeInfo = {
		val depType = stmt match {
			case _: ast.MethodCall => MethodCall
			case  _: ast.NewStmt | _: ast.AbstractAssign => SourceCode
			case _: ast.Exhale | _: ast.Assert => ExplicitAssertion
			case _: ast.Inhale | _: ast.Assume => ExplicitAssumption
			case _: ast.Fold | _: ast.Unfold | _: ast.Package | _: ast.Apply => Rewrite
			case _: ast.Quasihavoc | _: ast.Quasihavocall => DependencyType.Implicit
			case _ => DependencyType.make(AssumptionType.Unknown) /* TODO: should not happen */
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

	def matches(dependencyAnalysisJoinInfo: DependencyAnalysisJoinInfo) = {
		(this, dependencyAnalysisJoinInfo) match {
			case (SimpleDependencyAnalysisJoin(sourceInfo, joinType, edgeType), SimpleDependencyAnalysisJoin(sourceInfo1, joinType1, edgeType1)) =>
				sourceInfo.equals(sourceInfo1) && edgeType.equals(edgeType1)
		}
	}
}

case class EvalStackDependencyAnalysisJoin(joinType: JoinType, edgeType: EdgeType) extends DependencyAnalysisJoinInfo

case class SimpleDependencyAnalysisJoin(sourceInfo: AnalysisSourceInfo, joinType: JoinType, edgeType: EdgeType) extends DependencyAnalysisJoinInfo

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

case class SimpleDependencyAnalysisMerge(sourceInfo: AnalysisSourceInfo) extends DependencyAnalysisMergeInfo {
	override def isMerge: Boolean = true
}

case class CompositeDependencyAnalysisMergeInfo(sourceInfo1: AnalysisSourceInfo, sourceInfo2: AnalysisSourceInfo) extends DependencyAnalysisMergeInfo {
	override def isMerge: Boolean = true
}

object DependencyAnalysisMergeInfo {
	def attachExpMergeInfo(exps: Seq[ast.Exp], sourceInfo2: Option[AnalysisSourceInfo]): Seq[ast.Exp] = {
		exps.map(attachExpMergeInfo(_, sourceInfo2))
	}

	def attachExpMergeInfo(exp: ast.Exp, sourceInfo2: Option[AnalysisSourceInfo]): ast.Exp = {
		val expSourceInfo = AnalysisSourceInfo.createAnalysisSourceInfo(exp)
		attachExpMergeInfo(exp, expSourceInfo, sourceInfo2)
	}

	def attachExpMergeInfo(exp: ast.Exp, sourceInfo1: AnalysisSourceInfo, sourceInfo2: Option[AnalysisSourceInfo]): ast.Exp = {
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