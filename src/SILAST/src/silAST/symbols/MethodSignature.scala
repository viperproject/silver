package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.expressions.Expression
import silAST.source.SourceLocation

final class MethodSignature private[silAST](
    sl : SourceLocation,
    val parameters: List[ProgramVariable],
    val result: ProgramVariable,
    val precondition: List[Expression],
    val postcondition: List[Expression]
) extends ASTNode(sl)
{
  override def toString =
    "(" + parameters.toString + ") : " + result.toString +
      " requires " + precondition.toString +
      " ensures " + postcondition.toString

  override def subNodes = parameters ++ (result :: (precondition ++ postcondition))
}