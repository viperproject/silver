package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

final class ProgramVariableSequence private[silAST](
  sl : SourceLocation,
  val variables: Seq[ProgramVariable]
) extends ASTNode(sl)
{
  override def toString = "(" + variables.mkString(",") + ")"
  def subNodes: Seq[ASTNode] = variables

}