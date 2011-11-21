package symbols
import silAST.ExpressionNode

class ArgumentSequence( private val args : Seq[ExpressionNode]) {
	def asSeq() : Seq[ExpressionNode] = 
	{
		return args
	}
}