package silAST.expressions.util
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.DomainTerm

abstract class DArgumentSequence 
	extends ArgumentSequence
{
	override val args : Seq[DomainTerm]
	override def asSeq : Seq[DomainTerm] = args 
}