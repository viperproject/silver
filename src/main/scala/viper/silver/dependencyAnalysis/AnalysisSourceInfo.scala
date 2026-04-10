package viper.silver.dependencyAnalysis

import viper.silver.ast
import viper.silver.ast._

object AnalysisSourceInfo {
  def extractPositionString(p: Position): String = {
    p match {
      case NoPosition => "???"
      case filePos: AbstractSourcePosition => filePos.file.getFileName.toString + " @ line " + filePos.line
      case filePos: FilePosition => filePos.file.getFileName.toString + " @ line " + filePos.line
      case lineColumn: HasLineColumn => "line " + lineColumn.line.toString
      case VirtualPosition(identifier) => "label " + identifier
    }
  }

	def createAnalysisSourceInfo(node: ast.Node): AnalysisSourceInfo = {
		node match {
			case stmt: ast.Stmt => StmtAnalysisSourceInfo(stmt, stmt.pos)
			case exp: ast.Exp => ExpAnalysisSourceInfo(exp, exp.pos)
			case _ => createAnalysisSourceInfo("Unknown", NoPosition)
		}
	}

  def createAnalysisSourceInfo(description: String, pos: Position): AnalysisSourceInfo = StringAnalysisSourceInfo(description, pos)

}

trait AnalysisSourceInfo extends ast.Info {
  override def toString: String = getPositionString

  def getDescription: String

  def getLineNumber: Option[Int] = getPosition match {
    case column: HasLineColumn => Some(column.line)
    case _ => None
  }

  def getPositionString: String = {
    AnalysisSourceInfo.extractPositionString(getPosition)
  }

  def getPosition: Position


  def isAnalysisEnabled: Boolean = true


  override def comment: Seq[String] = Nil
  override def isCached: Boolean = false
}

case class NoAnalysisSourceInfo() extends AnalysisSourceInfo {
  override def getPosition: Position = NoPosition

  override def getDescription: String = ""

  override def equals(obj: Any): Boolean = false
}

case class ExpAnalysisSourceInfo(source: ast.Exp, pos: Position) extends AnalysisSourceInfo {

  override def toString: String = getDescription + " (" + super.toString + ")"

  override def getPosition: Position = pos

  override def isAnalysisEnabled: Boolean = true // DependencyAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)

  override def getDescription: String = source.toString.replaceAll("\n", "\t")
}

case class StmtAnalysisSourceInfo(source: ast.Stmt, pos: Position) extends AnalysisSourceInfo {

  override def toString: String = getDescription + " (" + super.toString + ")"
  override def getPosition: Position = pos

  override def isAnalysisEnabled: Boolean = true // DependencyAnalyzer.extractEnableAnalysisFromInfo(source.info).getOrElse(true)

  override def getDescription: String = source.toString().replaceAll("\n", "\t")
}

case class StringAnalysisSourceInfo(description: String, position: Position) extends AnalysisSourceInfo {
  override def toString: String = getDescription + " (" + getPositionString + ")"
  override def getPosition: Position = position

  override def getDescription: String = description.replaceAll("\n", "\t")
}

