package silAST.expressions.terms

import scala.collection.Seq
import silAST.ASTNode
import silAST.symbols.ArgumentSequence
import silAST.symbols.Function
import silAST.source.SourceLocation
import silAST.expressions.program.terms.GProgramTerm
import silAST.expressions.domain.terms.GDomainTerm
import silAST.expressions.assertion.terms.GTerm

class FunctionApplicationTerm[+T <: GTerm[T]](
	    sl:SourceLocation,
	    val function : Function, 
	    val arguments : ArgumentSequence[T] 
	) 
	extends GTerm[T](sl) with GDomainTerm[T] with GProgramTerm[T]
{

  override def toString(): String = { 
    return function.name + arguments.toString();
  }

  //override def subNodes(): Seq[ASTNode] = function :: arguments.asSeq.asInstanceOf[Seq[ASTNode]] 
  override def subTerms(): Seq[T] = arguments.asSeq

}