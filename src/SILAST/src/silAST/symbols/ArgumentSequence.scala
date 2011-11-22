package silAST.symbols
import silAST.expressions.terms.ExpressionNode
import silAST.expressions.terms.TermNode

class ArgumentSequence[+T <: TermNode[T]]( private val args : Seq[T]) {
	def asSeq() : Seq[T] = 
	{
		return args
	}
}