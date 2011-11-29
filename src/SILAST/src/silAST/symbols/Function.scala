package silAST.symbols

import silAST.ASTNode
import silAST.source.SourceLocation

class Function private [silAST](
  sl : SourceLocation,
  val name: String,
  val signature: FunctionSignature
) extends ASTNode(sl)
{
  override def subNodes = signature :: Nil
}