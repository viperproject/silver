package silAST

import scala.collection.Seq
import symbols.ArgumentSequence
import symbols.Function

class FunctionApplicationExpressionNode(sl:SourceLocation,val function : Function, val arguments : ArgumentSequence ) 
	extends ASTNode(sl) 
{

  override def toString(): String = { 
    return function.name + arguments.toString();
  }

  override def subNodes(): Seq[ExpressionNode] = { return arguments.asSeq }

}