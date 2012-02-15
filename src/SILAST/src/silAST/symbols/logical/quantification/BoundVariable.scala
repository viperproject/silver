package silAST.symbols.logical.quantification

import silAST.ASTNode
import silAST.types.DataType
import silAST.source.SourceLocation

sealed class BoundVariable private[silAST]
    (val name: String,val dataType: DataType)
    (val sourceLocation : SourceLocation)
  extends ASTNode
{
  override def toString: String = name

  override def equals(other : Any) : Boolean = {
    other match{
      case v : BoundVariable => v eq this
      case _ => false
    }
  }
  override def hashCode() : Int = name.hashCode()
}