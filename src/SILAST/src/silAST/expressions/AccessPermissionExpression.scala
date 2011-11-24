package silAST.expressions
import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.expressions.terms.Term
import silAST.expressions.permission.PermissionTerm

class AccessPermissionExpression( 
		sl : SourceLocation,
		val reference : Term,
		val permission : PermissionTerm
	) 
	extends Expression(sl) 
{
  override def toString : String = "acc(" + reference.toString() + "," + permission.toString() + ")"
  override def subNodes : Seq[ASTNode] = return reference :: (permission :: List.empty[ASTNode])

  override def subExpressions : Seq[Expression] = Nil
}