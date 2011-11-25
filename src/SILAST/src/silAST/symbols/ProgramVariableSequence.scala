package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class ProgramVariableSequence( 
		sl : SourceLocation,
		private val variables : Seq[ProgramVariable]
    ) 
    extends ASTNode(sl) 
{

//  def toString : String = "("

  def subNodes : Seq[ASTNode] = variables 

}