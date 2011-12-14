package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.types.DataTypeSequence

final class DomainPredicateSignature private[silAST](
                                                      sl: SourceLocation,
                                                      val argumentTypes: DataTypeSequence
                                                      ) extends ASTNode(sl) {
  def substitute(s: TypeSubstitution): DomainPredicateSignature = new DomainPredicateSignature(sl,argumentTypes.substitute(s))

  override def toString = argumentTypes.toString
}