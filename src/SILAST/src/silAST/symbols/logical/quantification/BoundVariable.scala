package silAST.symbols.logical.quantification

import silAST.ASTNode
import silAST.types.DataType
import silAST.AtomicNode
import silAST.source.SourceLocation

sealed class BoundVariable private[symbols](
                                      sl: SourceLocation,
                                      val name: String,
                                      val dataType: DataType
                                      ) extends ASTNode(sl) with AtomicNode {

  override def toString: String = name
}