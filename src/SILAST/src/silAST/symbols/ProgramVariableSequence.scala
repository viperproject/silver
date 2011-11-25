package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class ProgramVariableSequence extends ASTNode 
{
	val variables : Seq[ProgramVariable]
	
	def subNodes : Seq[ASTNode] = variables 

}