package silAST.symbols
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.TermNode

abstract class ArgumentSequence[+T <: TermNode[T]]( sl : SourceLocation, private val args : Seq[T]) extends ASTNode(sl){
	def asSeq() : Seq[T] = 
	{
		return args
	}
	
	override def subNodes() : Seq[T] = { return args}
}