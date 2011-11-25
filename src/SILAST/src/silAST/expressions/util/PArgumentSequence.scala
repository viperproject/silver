package silAST.expressions.util
import silAST.expressions.terms.ProgramTerm
import silAST.source.SourceLocation

abstract class PArgumentSequence extends ArgumentSequence
{
	override val args : Seq[ProgramTerm]
	override def asSeq : Seq[ProgramTerm] = args 
}