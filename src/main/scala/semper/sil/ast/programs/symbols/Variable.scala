package semper.sil.ast.programs.symbols

import semper.sil.ast.ASTNode
import semper.sil.ast.types.DataType

trait Variable extends ASTNode {
  def name: String

  def dataType: DataType
}
