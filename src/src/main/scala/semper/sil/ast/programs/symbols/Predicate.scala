package semper.sil.ast.programs.symbols

import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.Expression
import semper.sil.ast.source.SourceLocation

final class Predicate private [sil](
         val name: String
         )(val sourceLocation: SourceLocation,val factory : PredicateFactory, val comment:List[String])
  extends ASTNode
{
  override def toString = "predicate " + name + " = " + expression.toString

  private [sil] var pExpression: Option[Expression] = None

  def expression: Expression = pExpression.get

  override def equals(other: Any): Boolean = {
    other match {
      case p: Predicate => this eq p
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()

}