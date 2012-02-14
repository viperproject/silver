package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.types.DataTypeSequence

final class DomainPredicateSignature private[silAST](
                                                      val sourceLocation : SourceLocation,
                                                      val argumentTypes: DataTypeSequence
                                                      ) extends ASTNode {
  def substitute(s: TypeSubstitution): DomainPredicateSignature =
    new DomainPredicateSignature(sourceLocation,argumentTypes.substitute(s))

  override lazy val toString = argumentTypes.toString()
}