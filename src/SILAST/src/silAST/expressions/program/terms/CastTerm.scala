package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.DataType
import silAST.ASTNode
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.expressions.program.terms.GProgramTerm

class CastTerm[+T <: GLogicalTerm[T]](
    sl:SourceLocation, 
    val expression: T, 
    val newType : DataType)
    extends GLogicalTerm[T](sl) with GProgramTerm[T] 
{
  assert(expression!=null);
  assert(newType   !=null);

  override def toString(): String = { return "(" + expression + ") : " + newType.toString() }

  override def subNodes(): Seq[ASTNode] = { return expression :: newType :: Nil }

  override def subTerms(): Seq[T] = { return expression :: Nil }

}