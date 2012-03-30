package silAST.symbols.logical.quantification

import silAST.types.DataType
import silAST.source.SourceLocation
import silAST.programs.symbols.Variable

sealed class LogicalVariable private[silAST]
(val name: String, val dataType: DataType)
(val sourceLocation: SourceLocation)
  extends Variable {
  override def toString: String = name

  override def equals(other: Any): Boolean = {
    other match {
      case v: LogicalVariable => v eq this
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()
}