package silAST.programs.symbols

import silAST.ASTNode
import silAST.types.DataType

trait Variable extends ASTNode {
  def name: String

  def dataType: DataType
}
