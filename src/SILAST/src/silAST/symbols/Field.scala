package silAST.symbols
import silAST.ASTNode
import silAST.AtomicNode
import silAST.types.DataType
import silAST.types.NonReferenceDataType

sealed abstract class Field extends ASTNode with AtomicNode
{
	val name : String
	val dataType : DataType
	override def toString: String = name
}

abstract case class ReferenceField() extends Field 
{
}

abstract case class NonReferenceField() extends Field 
{
    	override val dataType : NonReferenceDataType
}