package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.TermNode
import silAST.symbols.DataType

class CastTermNode[+T <: TermNode[T]](
    sl:SourceLocation, 
    val expression: T, 
    val newType : DataType)
    extends TermNode[T](sl) 
{
  assert(expression!=null);
  assert(newType   !=null);

  override def toString(): String = { return "(" + expression + ") : " + newType.toString() }

  override def subNodes(): Seq[T] = { return expression :: Nil }

}