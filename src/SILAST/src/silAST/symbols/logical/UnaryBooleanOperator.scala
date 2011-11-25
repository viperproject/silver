package silAST.symbols.logical

import silAST.ASTNode
import scala.collection.Seq

sealed abstract class UnaryBooleanOperator extends ASTNode
{
  override def toString : String = name
  override def subNodes: Seq[ASTNode] = Nil

  def name : String
}

abstract case class NotOperator() extends UnaryBooleanOperator {

  def name : String = "!"

}