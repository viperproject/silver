package silAST.symbols.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

sealed abstract class UnaryBooleanOperator(sl : SourceLocation) extends ASTNode(sl) {

  override def toString : String = { return name }
  override def subNodes(): Seq[ASTNode] = { Nil }

  def name : String

}

case class NotOperator(sl:SourceLocation) extends UnaryBooleanOperator(sl) {

  def name : String = { return "!" }

}