package silAST.expressions.util
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.DomainTerm

abstract class DArgumentSequence( 
		sl : SourceLocation, 
		private val args : Seq[DomainTerm]
	) 
	extends ArgumentSequence(sl, args)
{
	override def asSeq : Seq[DomainTerm] = args 
}