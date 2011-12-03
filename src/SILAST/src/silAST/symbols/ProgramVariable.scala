package silAST.symbols

import silAST.ASTNode
import silAST.types.DataType
import silAST.source.SourceLocation

class ProgramVariable(
                       sl: SourceLocation,
                       val name: String,
                       val dataType: DataType
                       ) extends ASTNode(sl) {

  override def toString: String = name

  override def subNodes = dataType :: Nil
}