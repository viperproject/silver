package silAST.expressions.assertion
import silAST.source.SourceLocation
import silAST.expressions.program.ProgramExpression
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.ASTNode
import silAST.expressions.assertion.permission.PermissionTerm

class AccessExpression( 
		sl : SourceLocation,
		val reference : ProgramExpression,
		val permission : PermissionTerm
	) 
	extends AssertionExpression(sl) 
{
  override def toString() : String = { return "acc(" + reference.toString() + "," + permission.toString() + ")" }
  override def subNodes(): Seq[ASTNode] = { return reference :: (permission :: List.empty[ASTNode])}

  override def subExpressions(): Seq[ProgramExpression] = { return reference :: Nil}
}