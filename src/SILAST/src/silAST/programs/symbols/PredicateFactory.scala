package silAST.programs.symbols

import silAST.expressions.ExpressionFactory
import silAST.programs.{ProgramFactory, NodeFactory}
import silAST.expressions.Expression
import silAST.source.{noLocation, SourceLocation}
import silAST.types.ReferenceDataType
import silAST.domains.Domain


class PredicateFactory(
      private val programFactory : ProgramFactory,
      val sl : SourceLocation,
      val name : String
  ) extends NodeFactory with ExpressionFactory
{
  def compile() : Predicate =
  {
    require (expression != None)
    predicate
  }

  def setExpression(e : Expression) = {
    require (expression == None)
    require (expressions contains e)
    expression = Some(e)
    pPredicate.pExpression = Some(e)
//    val p = new Predicate(sl,name,e)
//    predicate = Some(p)
//    programFactory.predicates += predicate
  }

  val thisVar = new ProgramVariable(noLocation,"this",ReferenceDataType.referenceType)

  protected var expression : Option[Expression] = None

  protected[silAST] override val programVariables = Set(thisVar)
  protected[silAST] override val fields    = programFactory.fields
  protected[silAST] override val functions = programFactory.functions
  protected[silAST] override def predicates = programFactory.predicates

  protected[silAST] override def domainFunctions = programFactory.domainFunctions

  override val nullFunction = programFactory.nullFunction

  private[silAST] var pPredicate = new Predicate(sl,name) //: Option[Predicate] = None
  def predicate : Predicate = expression match {case None => throw new Exception case _ => pPredicate}

  override def trueExpression = programFactory.trueExpression
  override def falseExpression = programFactory.falseExpression

  override def dataTypes = programFactory.dataTypes union pDataTypes
  override def domainFactories = programFactory.domainFactories
}