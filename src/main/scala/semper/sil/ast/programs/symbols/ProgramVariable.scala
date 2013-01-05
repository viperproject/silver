package semper.sil.ast.programs.symbols

import semper.sil.ast.types.DataType
import semper.sil.ast.source.SourceLocation

class ProgramVariable(
                       val name: String,
                       val dataType: DataType
                       )(val sourceLocation: SourceLocation, val comment: List[String]) extends Variable {

  override def toString: String = name

  override def equals(other: Any): Boolean = {
    other match {
      case v: ProgramVariable => this eq v
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()
}