package silAST
import source.SourceLocation

abstract class ASTNode 
{
    val sourceLocation : SourceLocation //The location in source code
    
    override def toString : String  //String representation
	
	def subNodes : Seq[ASTNode]     //Ordered subnodes
	
	  
}