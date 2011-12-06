package silAST.programs.symbols

import silAST.ASTNode
import silAST.source.SourceLocation

final class Function private[silAST](
                                      sl: SourceLocation,
                                      val name: String,
                                      val signature: FunctionSignature
                                      ) extends ASTNode(sl) {
  override def toString = "function" + name + signature.toString

  override def subNodes = List(signature)
}