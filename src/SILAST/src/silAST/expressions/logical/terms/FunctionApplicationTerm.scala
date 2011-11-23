package silAST.expressions.terms

import scala.collection.Seq
import silAST.ASTNode
import silAST.symbols.ArgumentSequence
import silAST.symbols.Function
import silAST.source.SourceLocation
import silAST.expressions.domain.terms.DomainTerm
import silAST.expressions.program.terms.GProgramTerm
import silAST.expressions.domain.terms.GDomainTerm
import silAST.expressions.logical.terms.GLogicalTerm

class FunctionApplicationTerm[+T <: GLogicalTerm[T]](
	    sl:SourceLocation,
	    val function : Function, 
	    val arguments : ArgumentSequence[T] 
	) 
	extends GLogicalTerm[T](sl) with GDomainTerm[T] with GProgramTerm[T]
{

  override def toString(): String = { 
    return function.name + arguments.toString();
  }

  override def subNodes(): Seq[ASTNode] = { return (function :: Nil) ++ arguments.asSeq()  } 
  override def subTerms(): Seq[T] = { return arguments.asSeq() }

}