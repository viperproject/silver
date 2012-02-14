package silAST.domains

import silAST.ASTNode
import silAST.types.DataType
import silAST.types.DataTypeSequence
import silAST.source.SourceLocation

final class DomainFunctionSignature private[silAST](
                                                     val sourceLocation : SourceLocation,
                                                     val parameterTypes: DataTypeSequence,
                                                     val resultType: DataType
                                                     ) extends ASTNode {
  def substitute(s: TypeSubstitution): DomainFunctionSignature =
  {
    new DomainFunctionSignature(sourceLocation,parameterTypes.substitute(s),resultType.substitute(s))
  }

  override def toString = "(" + parameterTypes.toString + ")" + " : " + resultType.toString
}