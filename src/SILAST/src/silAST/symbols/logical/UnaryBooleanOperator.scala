package silAST.symbols.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.noLocation

sealed abstract class UnaryBooleanOperator private[silAST]() extends ASTNode(noLocation) {
  override def toString: String = name

  override def subNodes: Seq[ASTNode] = Nil

  def name: String
}

final case class NotOperator private[silAST]() extends UnaryBooleanOperator {

  def name: String = "!"

}