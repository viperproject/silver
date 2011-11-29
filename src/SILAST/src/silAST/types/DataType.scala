package silAST.types

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.{noLocation, SourceLocation}

sealed class DataType( sl : SourceLocation ) extends ASTNode(sl) {

}

case object ReferenceDataType extends DataType(noLocation)
{
}

/*object theReferenceDataType 
{
	val referenceType : ReferenceDataType = new ReferenceDataType(new SourceLocation) 
}
*/

case class NonReferenceDataType(sl: SourceLocation) extends DataType(sl) {
}