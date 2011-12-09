package silAST.programs.symbols

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.SourceLocation
import silAST.types.{referenceType, DataType, NonReferenceDataType}

sealed abstract class Field private[silAST](
                                             sl: SourceLocation,
                                             val name: String,
                                             val dataType: DataType
                                             ) extends ASTNode(sl) with AtomicNode {
  override def toString: String = "field " + name + " : " + dataType.toString
}

final case class ReferenceField private[silAST](
                                                 sl: SourceLocation,
                                                 override val name: String
                                                 ) extends Field(sl, name, referenceType) {
}

final case class NonReferenceField private[silAST](
                                                    sl: SourceLocation,
                                                    override val name: String,
                                                    override val dataType: NonReferenceDataType
                                                    ) extends Field(sl, name, dataType) {
}