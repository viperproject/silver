package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class ProgramVariableSequence(sl : SourceLocation) extends ASTNode(sl) {
  val variables: Seq[ProgramVariable]

  def subNodes: Seq[ASTNode] = variables

}