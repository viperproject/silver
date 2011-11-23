package silAST.expressions.program

import scala.collection.Seq
import silAST.expressions.logical.LogicalExpressionNode
import silAST.source.SourceLocation
import silAST.expressions.terms.GTermNode
import silAST.expressions.program.terms.GProgramTermNode
import silAST.expressions.program.terms.ProgramTermNode

abstract class ProgramExpressionNode( sl : SourceLocation ) 
		extends GProgramExpressionNode[ProgramTermNode](sl) 
{
  def subExpressions(): Seq[ProgramExpressionNode]
}