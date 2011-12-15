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
  def substitute(s: TypeSubstitution): DomainFunctionSignature =
  {
    new DomainFunctionSignature(sl,parameterTypes.substitute(s),resultType.substitute(s))
  }

  override def toString = "(" + parameterTypes.toString + ")" + " : " + resultType.toString
}