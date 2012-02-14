package silAST.programs.symbols

import silAST.ASTNode
import silAST.types.DataType
import silAST.source.SourceLocation

class ProgramVariable(
                       val sourceLocation : SourceLocation,
                       val name: String,
                       val dataType: DataType
                       ) extends ASTNode {

  override def toString: String = name
}