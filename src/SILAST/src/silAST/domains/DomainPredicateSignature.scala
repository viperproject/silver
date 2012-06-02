package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.types.DataTypeSequence

final class DomainPredicateSignature private[silAST](
                                                      val parameterTypes: DataTypeSequence
                                                      )(val sourceLocation: SourceLocation) extends ASTNode {
  def substitute(s: TypeVariableSubstitution): DomainPredicateSignature =
    new DomainPredicateSignature(parameterTypes.substitute(s))(sourceLocation)

  override lazy val toString = parameterTypes.toString()
  override val comment = Nil

  override def equals(other: Any): Boolean = {
    other match {
      case s: DomainPredicateSignature =>
        parameterTypes == s.parameterTypes
      case _ => false
    }
  }

  override def hashCode(): Int = parameterTypes.hashCode()
}