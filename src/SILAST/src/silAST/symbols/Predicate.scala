package silAST.symbols

import silAST.ASTNode
import silAST.expressions.Expression
import silAST.source.SourceLocation

class Predicate private[silAST](
    sl : SourceLocation,
    val name: String,
    val expression: Expression
) extends ASTNode(sl)
{
  override def subNodes = expression :: Nil
}