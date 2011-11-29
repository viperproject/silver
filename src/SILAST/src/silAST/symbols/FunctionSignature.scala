package silAST.symbols

import silAST.ASTNode
import silAST.expressions.Expression
import silAST.expressions.terms.Term
import silAST.types.DataType

abstract class FunctionSignature extends ASTNode {
  val receiverType: DataType
  val argumentTypes: DataTypeSequence
  val resultType: DataType
  val precondition: Expression
  val postcondition: Expression
  val terminationMeasure: Term
}