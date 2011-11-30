package silAST.symbols

import silAST.ASTNode
import silAST.expressions.util.ExpressionSequence
import silAST.expressions.terms.Term
import silAST.types.DataType
import silAST.source.SourceLocation

final class FunctionSignature private [silAST](
      sl : SourceLocation,
      val receiverType: DataType,
      val argumentTypes: DataTypeSequence,
      val resultType: DataType,
      val precondition: ExpressionSequence,
      val postcondition: ExpressionSequence,
      val terminationMeasure : Term
 ) extends ASTNode(sl)
{
  override def toString =
    argumentTypes.toString + " : " + resultType.toString +
    (for (p <- precondition.asSeq ) yield "requires " + p.toString).mkString("\n") +
    (for (p <- postcondition.asSeq) yield "ensures " + p.toString).mkString("\n") +
    "measure "  + terminationMeasure.toString

  override def subNodes = receiverType :: argumentTypes :: resultType ::  (precondition ++ postcondition ++ (terminationMeasure :: Nil))
}