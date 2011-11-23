package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.GExpression
import silAST.symbols.DataType
import silAST.ASTNode

abstract class GTerm[+T <: GTerm[T]](sl:SourceLocation) extends ASTNode(sl)
 {

  def subTerms(): Seq[GTerm[T]]
  
//  def dataType : DataType

}