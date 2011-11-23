package silAST.symbols.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class UnaryBooleanOperatorNode(sl : SourceLocation) extends ASTNode(sl) {

  override def toString : String = { return name }
  override def subNodes(): Seq[ASTNode] = { Nil }

  def name : String

}