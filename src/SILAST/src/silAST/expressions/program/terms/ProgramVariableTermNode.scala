package silAST.expressions.terms
import silAST.AtomicNode
import silAST.symbols.ProgramVariable
import silAST.source.SourceLocation
import silAST.expressions.program.terms.GProgramTermNode
import silAST.ASTNode

class ProgramVariableTermNode(
		sl : SourceLocation, 
		val variable : ProgramVariable 
	) 
	extends GProgramTermNode[ProgramVariableTermNode](sl) 
	with AtomicTermNode[ProgramVariableTermNode]
{
	assert(variable!=null);
	
	override def toString(): String = { return variable.name; }
	override def subNodes : Seq[ASTNode] = { return variable :: Nil }
}