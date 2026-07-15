// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silver.dependencyAnalysis

import viper.silver.ast

import java.util.concurrent.atomic.AtomicInteger

object DependencyAnalysisSourceInfo {
  def extractPositionString(p: ast.Position): String = {
    p match {
      case ast.NoPosition => "???"
      case filePos: ast.AbstractSourcePosition => filePos.file.getFileName.toString + " @ line " + filePos.line
      case filePos: ast.FilePosition => filePos.file.getFileName.toString + " @ line " + filePos.line
      case lineColumn: ast.HasLineColumn => "line " + lineColumn.line.toString
      case ast.VirtualPosition(identifier) => "label " + identifier
    }
  }

  def createAnalysisSourceInfo(node: ast.Node): DependencyAnalysisSourceInfo = {
    node match {
      case n: ast.Infoed if n.info.getUniqueInfo[DependencyAnalysisSourceInfo].nonEmpty =>
        n.info.getUniqueInfo[DependencyAnalysisSourceInfo].get
      case stmt: ast.Stmt => StmtDependencyAnalysisSourceInfo(stmt, stmt.pos)
      case exp: ast.Exp => ExpDependencyAnalysisSourceInfo(exp, exp.pos)
      case _ => createAnalysisSourceInfo("Unknown", ast.NoPosition)
    }
  }

  def createAnalysisSourceInfo(description: String, pos: ast.Position): DependencyAnalysisSourceInfo = StringDependencyAnalysisSourceInfo(description, pos)

}

/**
 * The source info corresponds to the representation of dependency nodes on the user-level. That is, all lower level nodes
 * with the same source info are ultimately presented to the user as one single node.
 * Each Viper node should be associated with such a source info such that lifting the lower level graph to the user level works correctly.
 */
trait DependencyAnalysisSourceInfo extends ast.Info {
  override def toString: String = getPositionString

  def getDescription: String

  def getLineNumber: Option[Int] = getPosition match {
    case column: ast.HasLineColumn => Some(column.line)
    case _ => None
  }

  def getPositionString: String = {
    DependencyAnalysisSourceInfo.extractPositionString(getPosition)
  }

  def getPosition: ast.Position

  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

/**
 * Denotes the absence of a source info. Should only be used for internal nodes that are hidden from users anyways.
 */
case class NoDependencyAnalysisSourceInfo() extends DependencyAnalysisSourceInfo {
  override def getPosition: ast.Position = ast.NoPosition

  override def getDescription: String = ""

  override def equals(obj: Any): Boolean = false
}

/**
 * Denotes a node that has a Viper-level expression as its source.
 */
case class ExpDependencyAnalysisSourceInfo(source: ast.Exp, pos: ast.Position) extends DependencyAnalysisSourceInfo {

  override def toString: String = getDescription + " (" + super.toString + ")"

  override def getPosition: ast.Position = pos

  override def getDescription: String = source.toString.replaceAll("\n", "\t")
}

/**
 * Denotes a node that has a Viper-level statement as its source.
 */
case class StmtDependencyAnalysisSourceInfo(source: ast.Stmt, pos: ast.Position) extends DependencyAnalysisSourceInfo {

  override def toString: String = getDescription + " (" + super.toString + ")"
  override def getPosition: ast.Position = pos

  override def getDescription: String = source.toString().replaceAll("\n", "\t")
}

/**
 * Can be used to create custom dependency nodes (with custom source info). We use this mainly for internal nodes to give them a
 * description for debugging purposes.
 */
case class StringDependencyAnalysisSourceInfo(description: String, position: ast.Position = ast.NoPosition) extends DependencyAnalysisSourceInfo {
  override def toString: String = getDescription + " (" + getPositionString + ")"
  override def getPosition: ast.Position = position

  override def getDescription: String = description.replaceAll("\n", "\t")
}

object StringDependencyAnalysisSourceInfo {
  private val id: AtomicInteger = new AtomicInteger(0)
  def createUnique(description: String, position: ast.Position = ast.NoPosition): StringDependencyAnalysisSourceInfo =
    StringDependencyAnalysisSourceInfo(s"$description-${id.getAndIncrement()}", position)
}

