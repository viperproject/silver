package silAST.programs.symbols

import silAST.programs.ProgramFactory
import silAST.expressions.Expression
import silAST.source.SourceLocation


class PredicateFactory private[silAST](
                                        programFactory: ProgramFactory,
                                        val sl: SourceLocation,
                                        val name: String
                                        ) extends SymbolFactory[Predicate](programFactory) {
  override def compile(): Predicate = {
    require(pPredicate.pExpression != None)
    predicate
  }

  def setExpression(e: Expression) {
    require(pPredicate.pExpression == None)
    require(expressions contains e)
    pPredicate.pExpression = Some(e)
  }

  private[silAST] var pPredicate = new Predicate(sl, name) //: Option[Predicate] = None
  def predicate: Predicate = pPredicate.pExpression match {
    case None => throw new Exception
    case _ => pPredicate
  }

  protected[silAST] override def permissionVariables = Set()
}