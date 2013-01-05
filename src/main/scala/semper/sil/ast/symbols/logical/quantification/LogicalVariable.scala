package semper.sil.ast.symbols.logical.quantification

import semper.sil.ast.types.DataType
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.programs.symbols.Variable

sealed class LogicalVariable private[sil]
(val name: String, val dataType: DataType)
(val sourceLocation: SourceLocation, val comment: List[String])
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