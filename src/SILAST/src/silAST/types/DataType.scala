package silAST.types
import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.AtomicNode

abstract sealed class DataType extends ASTNode{

}

abstract case class ReferenceDataType(sl : SourceLocation ) extends DataType with AtomicNode
{
}

/*object theReferenceDataType 
{
	val referenceType : ReferenceDataType = new ReferenceDataType(new SourceLocation) 
}
*/

abstract case class NonReferenceDataType(sl : SourceLocation ) extends DataType
{
}