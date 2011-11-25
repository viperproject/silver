package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq

abstract class ProgramVariableSequence extends ASTNode
{
	val variables : Seq[ProgramVariable]
	
	def subNodes : Seq[ASTNode] = variables 

}