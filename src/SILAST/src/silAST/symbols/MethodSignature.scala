package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.expressions.Expression
import silAST.source.SourceLocation

class MethodSignature private[silAST](
    sl : SourceLocation,
    val arguments: List[ProgramVariable],
    val result: ProgramVariable,
    val precondition: List[Expression],
    val postcondition: List[Expression]
) extends ASTNode(sl)
{
   override def subNodes = arguments ++ (result :: (precondition ++ postcondition))
}