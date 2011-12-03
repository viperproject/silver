package silAST.symbols

import silAST.ASTNode
import silAST.source.SourceLocation

final class Method private[silAST](
                                    sl: SourceLocation,
                                    val name: String,
                                    val signature: MethodSignature,
                                    val implementations: Set[Implementation]
                                    ) extends ASTNode(sl) {
  override def toString = "method " + name + signature.toString

  override def subNodes = signature :: implementations.toList
}