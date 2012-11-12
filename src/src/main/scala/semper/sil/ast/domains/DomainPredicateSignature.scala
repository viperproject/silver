package semper.sil.ast.domains

import semper.sil.ast.ASTNode
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.types.DataTypeSequence

final class DomainPredicateSignature private [sil](
                                                      val parameterTypes: DataTypeSequence
                                                      )(val sourceLocation: SourceLocation) extends ASTNode {
  def substitute(s: TypeVariableSubstitution): DomainPredicateSignature =
    new DomainPredicateSignature(parameterTypes.substitute(s))(sourceLocation)

  override lazy val toString = "(" + parameterTypes.mkString("",",","") + ")"
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