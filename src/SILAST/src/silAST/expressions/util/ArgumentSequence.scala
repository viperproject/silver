package silAST.expressions.util
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.Term

abstract class ArgumentSequence( sl : SourceLocation, private val args : Seq[Term]) extends ASTNode(sl){
	def asSeq : Seq[Term] = args 
	
	override def subNodes : Seq[ASTNode] = args
}