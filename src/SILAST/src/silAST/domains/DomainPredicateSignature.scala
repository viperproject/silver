package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.types.DataTypeSequence

final class DomainPredicateSignature private[silAST](
                                                      sl: SourceLocation,
                                                      val argumentTypes: DataTypeSequence
                                                      ) extends ASTNode(sl) {
  override def toString = argumentTypes.toString

  override def subNodes = argumentTypes :: Nil
}