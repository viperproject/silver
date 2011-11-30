package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.programs.ProgramFactory

final class ProgramVariableSequence private[silAST](
  sl : SourceLocation,
  programFactory : ProgramFactory,
  val variables: Seq[ProgramVariable]
) extends ASTNode(sl,programFactory)
{
  def subNodes: Seq[ASTNode] = variables

}