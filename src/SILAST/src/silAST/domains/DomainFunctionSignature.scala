package silAST.domains

import silAST.ASTNode
import silAST.types.DataType
import silAST.types.DataTypeSequence
import silAST.source.SourceLocation

final class DomainFunctionSignature private[silAST](
                                                     sl: SourceLocation,
                                                     val parameterTypes: DataTypeSequence,
                                                     val resultType: DataType
                                                     ) extends ASTNode(sl) {
  require (parameterTypes!=null)
  require (resultType !=null)
  override def toString = "(" + parameterTypes.toString + ")" + " : " + resultType.toString
}