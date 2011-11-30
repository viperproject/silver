package silAST

import programs.ProgramFactory
import source.SourceLocation

abstract class ASTNode protected[silAST](
  val sourceLocation : SourceLocation,
  private [silAST] val programFactory : ProgramFactory
)
{
  override def toString: String //String representation

  def subNodes: Seq[ASTNode] //Ordered subnodes
}