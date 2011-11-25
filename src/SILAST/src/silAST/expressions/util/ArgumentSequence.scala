package silAST.expressions.util
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.Term

abstract class ArgumentSequence extends ASTNode{

	def asSeq : Seq[Term] = args 
	val args : Seq[Term]

	override def subNodes : Seq[ASTNode] = args
}