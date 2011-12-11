package silAST.symbols.logical.quantification

import silAST.ASTNode
import silAST.types.DataType
import silAST.source.SourceLocation

sealed class BoundVariable private[silAST](
                                            sl: SourceLocation,
                                            val name: String,
                                            val dataType: DataType
                                            ) extends ASTNode(sl) {

  override def toString: String = name
}