package silAST
import source.SourceLocation

abstract class ASTNode(
    val sourceLocation : SourceLocation //The location in source code
) {
	assert(sourceLocation != null);
	
	override def toString() : String;  //String representation
	
	def subNodes() : Seq[ASTNode];     //Ordered subnodes
	
	  
}