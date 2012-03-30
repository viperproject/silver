package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.types.{DataType, DataTypeSequence}

final class DomainFunctionSignature private[silAST](
                                                     val parameterTypes: DataTypeSequence,
                                                     val resultType: DataType
                                                     )(val sourceLocation: SourceLocation) extends ASTNode {
  def substitute(s: TypeVariableSubstitution): DomainFunctionSignature = {
    new DomainFunctionSignature(parameterTypes.substitute(s), resultType.substitute(s))(sourceLocation)
  }

  override def toString = "(" + parameterTypes.toString + ")" + " : " + resultType.toString

  override def equals(other: Any): Boolean = {
    other match {
      case s: DomainFunctionSignature =>
        parameterTypes == s.parameterTypes &&
          resultType == s.resultType
      case _ => false
    }
  }

  override def hashCode(): Int = parameterTypes.hashCode() + resultType.hashCode()
}