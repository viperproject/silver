package silAST.symbols.logical.quantification

import silAST.ASTNode
import silAST.types.DataType
import silAST.source.SourceLocation

sealed class BoundVariable private[silAST](
                                            val sourceLocation : SourceLocation,
                                            val name: String,
                                            val dataType: DataType
                                            ) extends ASTNode {

  override def toString: String = name
}