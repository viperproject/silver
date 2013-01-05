package semper.sil.ast.domains

import semper.sil.ast.ASTNode
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.types.{DataType, DataTypeSequence}

final class DomainFunctionSignature private[sil](
                                                  val parameterTypes: DataTypeSequence,
                                                  val resultType: DataType
                                                  )(val sourceLocation: SourceLocation) extends ASTNode {
  def substitute(s: TypeVariableSubstitution): DomainFunctionSignature = {
    new DomainFunctionSignature(parameterTypes.substitute(s), resultType.substitute(s))(sourceLocation)
  }

  override val comment = Nil

  override def toString = "(" + parameterTypes.mkString("", ",", "") + ")" + " : " + resultType.toString

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