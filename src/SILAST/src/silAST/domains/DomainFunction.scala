package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation

class DomainFunction private[silAST](
    sl : SourceLocation,
    val name: String,
    val signature : DomainFunctionSignature
) extends ASTNode(sl) {
  override def subNodes = signature :: Nil
}