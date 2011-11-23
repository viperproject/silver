package silAST.programs

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.ASTNode

abstract class Program(
		val sl : SourceLocation
	) extends ASTNode(sl) 
{

}