package silAST.types
import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.AtomicNode

abstract sealed class DataType( sl : SourceLocation ) extends ASTNode(sl) {

}

case class ReferenceDataType( sl : SourceLocation ) extends DataType(sl) with AtomicNode
{
}

object theReferenceDataType 
{
	val referenceType : ReferenceDataType = new ReferenceDataType(new SourceLocation) 
}


abstract case class NonReferenceDataType( sl : SourceLocation ) extends DataType(sl) 
{
}