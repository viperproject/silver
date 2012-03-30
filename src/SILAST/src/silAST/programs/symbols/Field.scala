package silAST.programs.symbols

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.types.{referenceType, DataType, NonReferenceDataType}

sealed abstract class Field private[silAST] extends ASTNode {
  def name: String

  def dataType: DataType

  override def toString: String = "field " + name + " : " + dataType.toString
}

final case class ReferenceField private[silAST](

                                                 name: String
                                                 )(override val sourceLocation: SourceLocation) extends Field {
  override val dataType = referenceType
}

final case class NonReferenceField private[silAST](

                                                    name: String,
                                                    dataType: NonReferenceDataType
                                                    )(override val sourceLocation: SourceLocation) extends Field {
}