package silAST.symbols

import silAST.ASTNode
import silAST.expressions.Expression
import silAST.expressions.terms.Term
import silAST.types.DataType
import silAST.source.SourceLocation

class FunctionSignature private [silAST](
      sl : SourceLocation,
      val receiverType: DataType,
      val argumentTypes: DataTypeSequence,
      val resultType: DataType,
      val precondition: List[Expression],
      val postcondition: List[Expression],
      val terminationMeasure : Term
 ) extends ASTNode(sl)
{
  override def subNodes = receiverType :: argumentTypes :: resultType ::  (precondition ++ postcondition ++ (terminationMeasure :: Nil))
}