package semper.sil.ast.symbols.logical.quantification

import semper.sil.ast.types.DataType
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.programs.symbols.Variable

case class LogicalVariable(val name: String, val dataType: DataType)
                          (val sourceLocation: SourceLocation, val comment: List[String])
    extends Variable {

  override def toString: String = name
}