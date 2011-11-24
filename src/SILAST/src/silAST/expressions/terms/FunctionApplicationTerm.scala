package silAST.expressions.terms
import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.expressions.domain.terms.GDomainTerm
import silAST.expressions.program.terms.GProgramTerm
import silAST.symbols.ArgumentSequence
import silAST.symbols.Function

abstract class FunctionApplicationTerm[+T <: GTerm[T]](
	    sl:SourceLocation,
	    val function : Function, 
	    val arguments : ArgumentSequence[T] 
	) 
	extends GTerm[T](sl) //with GDomainTerm[T] with GProgramTerm[T]
{

  override def toString : String = function.name + arguments.toString
  

//  override def subNodes(): Seq[ASTNode] = List(function) :: arguments.asSeq 
//  override def subTerms : Seq[T] = arguments.asSeq

}
