package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.ExpressionNode
import silAST.symbols.DataType
import silAST.ASTNode

abstract class TermNode[+T <: TermNode[T]](sl:SourceLocation) extends ASTNode(sl) {

  def subTerms(): Seq[T]
  
//  def dataType : DataType

}