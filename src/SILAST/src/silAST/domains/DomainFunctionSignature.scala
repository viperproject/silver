package silAST.domains

import silAST.ASTNode
import silAST.types.DataType
import silAST.symbols.DataTypeSequence
import silAST.source.SourceLocation

final class DomainFunctionSignature private[silAST](
                                                     sl: SourceLocation,
                                                     val parameterTypes: DataTypeSequence,
                                                     val resultType: DataType
                                                     ) extends ASTNode(sl) {
  override def toString = "(" + parameterTypes.toString + ")" + " : " + resultType.toString

  override def subNodes = parameterTypes :: resultType :: Nil
}