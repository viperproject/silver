package silAST

import scala.collection.Seq
import source.SourceLocation

abstract class Program(
		val sl : SourceLocation
	) extends ASTNode(sl) 
{

}