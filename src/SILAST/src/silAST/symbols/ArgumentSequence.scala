package silAST.symbols
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.GLogicalTerm

abstract class ArgumentSequence[+T <: GLogicalTerm[T]]( sl : SourceLocation, private val args : Seq[T]) extends ASTNode(sl){
	def asSeq : Seq[T] = args 
	
	override def subNodes : Seq[T] = args
}