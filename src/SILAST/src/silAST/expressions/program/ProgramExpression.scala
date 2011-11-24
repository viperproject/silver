package silAST.expressions.program

import scala.collection.Seq
import silAST.expressions.logical.LogicalExpression
import silAST.source.SourceLocation
import silAST.expressions.program.terms.GProgramTerm
import silAST.expressions.program.terms.ProgramTerm

abstract class ProgramExpression( sl : SourceLocation ) 
		extends GProgramExpression[ProgramTerm](sl) 
{
  def subExpressions(): Seq[ProgramExpression]
}
