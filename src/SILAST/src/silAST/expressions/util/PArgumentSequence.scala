package silAST.expressions.util
import silAST.expressions.terms.ProgramTerm
import silAST.source.SourceLocation

abstract class PArgumentSequence( 
		sl : SourceLocation, 
		private val args : Seq[ProgramTerm]
	) 
	extends ArgumentSequence(sl, args)
{
	override def asSeq : Seq[ProgramTerm] = args 
}