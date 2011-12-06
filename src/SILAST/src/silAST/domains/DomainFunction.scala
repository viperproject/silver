package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation

final class DomainFunction private[silAST](
                                            sl: SourceLocation,
                                            val name: String,
                                            val signature: DomainFunctionSignature
                                            ) extends ASTNode(sl) {
  override def toString = "function " + name + signature.toString

  override def subNodes = signature :: Nil
}