package symbols
import silAST.expressions.terms.ExpressionNode

class ArgumentSequence( private val args : Seq[ExpressionNode]) {
	def asSeq() : Seq[ExpressionNode] = 
	{
		return args
	}
}