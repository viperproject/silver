package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.DataType
import silAST.ASTNode

class CastTermNode[+T <: GTermNode[T]](
    sl:SourceLocation, 
    val expression: T, 
    val newType : DataType)
    extends GTermNode[T](sl) 
{
  assert(expression!=null);
  assert(newType   !=null);

  override def toString(): String = { return "(" + expression + ") : " + newType.toString() }

  override def subNodes(): Seq[ASTNode] = { return expression :: newType :: Nil }

  override def subTerms(): Seq[T] = { return expression :: Nil }

}