package silAST.programs.symbols

import silAST.expressions.ExpressionFactory
import silAST.programs.{ProgramFactory, NodeFactory}
import silAST.expressions.Expression
import silAST.source.{noLocation, SourceLocation}
import silAST.types.ReferenceDataType


class PredicateFactory(
      private val pf : ProgramFactory,
      val sl : SourceLocation,
      val name : String
  ) extends NodeFactory with ExpressionFactory
{
  def setExpression(e : Expression) = {
    require (expression == None)
    require (expressions contains e)
    expression = Some(e)
    val p = new Predicate(sl,name,e)
    predicate = Some(p)
    pf.predicates += p
  }

  protected var expression : Option[Expression] = None

  protected[silAST] override val programVariables =
    Set(new ProgramVariable(noLocation,"this",ReferenceDataType.referenceType))
  protected[silAST] override val fields    = pf.fields
  protected[silAST] override val functions = pf.functions
  protected[silAST] override val predicates = pf.predicates

  private var predicate : Option[Predicate] = None
}