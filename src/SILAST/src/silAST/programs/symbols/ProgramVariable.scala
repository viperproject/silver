package silAST.programs.symbols

import silAST.ASTNode
import silAST.types.DataType
import silAST.source.SourceLocation

class ProgramVariable(

                       val name: String,
                       val dataType: DataType
                       )(val sourceLocation : SourceLocation) extends ASTNode {

  override def toString: String = name

  override def equals(other : Any) : Boolean =
  {
    other match{
      case v : ProgramVariable => this eq  v
      case _ => false
    }
  }
  override def hashCode() : Int = name.hashCode()
}