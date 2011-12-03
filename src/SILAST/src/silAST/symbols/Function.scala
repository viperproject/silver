package silAST.symbols

import silAST.ASTNode
import silAST.source.SourceLocation

final class Function private[silAST](
                                      sl: SourceLocation,
                                      val name: String,
                                      val signature: FunctionSignature
                                      ) extends ASTNode(sl) {
  override def toString = signature.receiverType.toString + "." + name + signature.toString

  override def subNodes = signature :: Nil
}