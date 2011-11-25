package silAST.symbols
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.AtomicNode
import silAST.types.DataType
import silAST.types.ReferenceDataType
import silAST.types.NonReferenceDataType
import silAST.types.theReferenceDataType

sealed abstract class Field( 
		sl : SourceLocation, 
		val name : String, 
		val dataType : DataType
    ) extends ASTNode(sl) with AtomicNode
{
	override def toString() : String = name
}

case class ReferenceField( 
		sl : SourceLocation, 
		override val name : String 
    ) extends Field(sl,name,theReferenceDataType.referenceType) 
{
}

case class NonReferenceField( 
		sl : SourceLocation, 
		override val name : String,
		override val dataType : NonReferenceDataType
    ) extends Field(sl,name,dataType) 
{
}