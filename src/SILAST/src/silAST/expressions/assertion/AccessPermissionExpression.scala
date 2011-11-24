package silAST.expressions.assertion
import silAST.source.SourceLocation
import silAST.expressions.program.ProgramExpression
import silAST.ASTNode
import silAST.expressions.assertion.permission.PermissionTerm
import silAST.expressions.assertion.terms.Term

class AccessPermissionExpression( 
		sl : SourceLocation,
		val reference : Term,
		val permission : PermissionTerm
	) 
	extends GExpression[Term](sl) 
{
  override def toString : String = "acc(" + reference.toString() + "," + permission.toString() + ")"
  override def subNodes : Seq[ASTNode] = return reference :: (permission :: List.empty[ASTNode])

  override def subExpressions : Seq[GExpression[Term]] = Nil
}