package silAST.symbols

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.SourceLocation
import silAST.types.{ReferenceDataType, DataType, NonReferenceDataType}

sealed abstract class Field private[silAST](
    sl: SourceLocation,
    val name: String,
    val dataType: DataType
  ) extends ASTNode(sl) with AtomicNode
{
  override def toString: String = name
}

case class ReferenceField(
           sl: SourceLocation,
           name: String
    ) extends Field(sl,name,ReferenceDataType)
{
}

case class NonReferenceField(
          sl: SourceLocation,
          name: String,
          dataType: NonReferenceDataType
      ) extends Field(sl,name,dataType)
{
}