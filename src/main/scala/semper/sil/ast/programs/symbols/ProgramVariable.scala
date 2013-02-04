package semper.sil.ast.programs.symbols

import semper.sil.ast.types.DataType
import semper.sil.ast.source.SourceLocation

case class ProgramVariable(val name: String, val dataType: DataType)
                          (val sourceLocation: SourceLocation, val comment: List[String])
    extends Variable {

  override def toString: String = name
}