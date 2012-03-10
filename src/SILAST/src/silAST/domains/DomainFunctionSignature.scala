package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.types.{TypeVariable, DataType, DataTypeSequence}

final class DomainFunctionSignature private[silAST](
                                                     val sourceLocation : SourceLocation,
                                                     val parameterTypes: DataTypeSequence,
                                                     val resultType: DataType
                                                     ) extends ASTNode {
  def substitute(s: TypeVariableSubstitution): DomainFunctionSignature =
  {
    new DomainFunctionSignature(sourceLocation,parameterTypes.substitute(s),resultType.substitute(s))
  }

  override def toString = "(" + parameterTypes.toString + ")" + " : " + resultType.toString

  override def equals(other : Any) : Boolean =
  {
    other match{
      case s : DomainFunctionSignature => 
        parameterTypes == s.parameterTypes &&
        resultType == s.resultType
      case _ => false
    }
  }
  override def hashCode() : Int = parameterTypes.hashCode() + resultType.hashCode()
}