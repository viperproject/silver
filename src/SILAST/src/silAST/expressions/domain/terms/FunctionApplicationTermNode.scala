package silAST.expressions.domain.terms

import scala.collection.Seq
import silAST.ASTNode
import silAST.symbols.ArgumentSequence
import silAST.symbols.Function
import silAST.source.SourceLocation
import silAST.expressions.terms.GTermNode

class FunctionApplicationTermNode[+T <: GTermNode[T]](
	    sl:SourceLocation,
	    val function : Function, 
	    val arguments : ArgumentSequence[T] 
	) 
	extends GTermNode[T](sl) 
{

  override def toString(): String = { 
    return function.name + arguments.toString();
  }

  override def subNodes(): Seq[ASTNode] = { return (function :: Nil) ++ arguments.asSeq()  } 
  override def subTerms(): Seq[T] = { return arguments.asSeq() }

}