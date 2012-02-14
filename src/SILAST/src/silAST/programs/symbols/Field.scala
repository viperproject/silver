package silAST.programs.symbols

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.types.{referenceType, DataType, NonReferenceDataType}

sealed abstract class Field private[silAST] extends ASTNode{
  def name: String
  def dataType: DataType

  override def toString: String = "field " + name + " : " + dataType.toString
}

final case class ReferenceField private[silAST](
                                                 sourceLocation : SourceLocation,
                                                 name: String
                                                 ) extends Field
{
  override val dataType = referenceType
}

final case class NonReferenceField private[silAST](
                                                    sourceLocation : SourceLocation,
                                                    name: String,
                                                    dataType: NonReferenceDataType
                                                    ) extends Field
{
}