package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.GExpressionNode
import silAST.symbols.DataType
import silAST.ASTNode

abstract class GTermNode[+T <: GTermNode[T]](sl:SourceLocation) extends ASTNode(sl) {

  def subTerms(): Seq[GTermNode[T]]
  
//  def dataType : DataType

}