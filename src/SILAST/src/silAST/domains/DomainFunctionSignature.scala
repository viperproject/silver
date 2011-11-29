package silAST.domains

import silAST.ASTNode
import silAST.types.DataType
import silAST.symbols.DataTypeSequence
import silAST.source.SourceLocation

class DomainFunctionSignature private[silAST](
  sl : SourceLocation,
  val argumentTypes: DataTypeSequence,
  val resultType: DataType
) extends ASTNode(sl)
{
  override def SubNodes = argumentTypes :: resultType :: Nil
}