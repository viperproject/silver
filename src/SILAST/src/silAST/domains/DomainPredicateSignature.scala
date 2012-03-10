package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.types.DataTypeSequence

final class DomainPredicateSignature private[silAST](
                                                      val sourceLocation : SourceLocation,
                                                      val parameterTypes: DataTypeSequence
                                                      ) extends ASTNode {
  def substitute(s: TypeVariableSubstitution): DomainPredicateSignature =
    new DomainPredicateSignature(sourceLocation,parameterTypes.substitute(s))

  override lazy val toString = parameterTypes.toString()

  override def equals(other : Any) : Boolean =
  {
    other match{
      case s : DomainPredicateSignature =>
        parameterTypes == s.parameterTypes
      case _ => false
    }
  }
  override def hashCode() : Int = parameterTypes.hashCode()
}