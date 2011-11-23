package silAST.expressions.assertion
import silAST.source.SourceLocation
import silAST.expressions.program.ProgramExpressionNode
import silAST.expressions.logical.terms.LogicalTermNode
import silAST.ASTNode
import silAST.expressions.assertion.permission.PermissionTerm

class PermissionTermNode( 
		sl : SourceLocation,
		val reference : ProgramExpressionNode[LogicalTermNode],
		val permission : PermissionTerm
	) 
	extends AssertionExpressionNode(sl) 
{
  override def toString() : String = { return "acc(" + reference.toString() + "," + permission.toString() + ")" }
  override def subNodes(): Seq[ASTNode] = { return reference :: permission :: Nil}

  override def subExpressions(): Seq[ProgramExpressionNode[LogicalTermNode]] = { return reference :: Nil}
}