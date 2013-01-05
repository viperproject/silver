package semper.sil.ast.programs.symbols

import semper.sil.ast.programs.ProgramFactory
import semper.sil.ast.expressions.Expression
import semper.sil.ast.source.SourceLocation


class PredicateFactory private[sil](
                                     programFactory: ProgramFactory,
                                     val name: String
                                     )(val sourceLocation: SourceLocation, val comment: List[String])
  extends SymbolFactory[Predicate](programFactory) {
  override def compile(): Predicate = {
    require(pPredicate.pExpression != None)
    predicate
  }

  def setExpression(e: Expression) {
    require(pPredicate.pExpression == None)
    migrate(e)
    require(expressions contains e)
    pPredicate.pExpression = Some(e)
  }

  private[sil] var pPredicate = new Predicate(name)(sourceLocation, this, comment)

  def predicate: Predicate = pPredicate.pExpression match {
    case None => throw new Exception
    case _ => pPredicate
  }

  override def typeVariables = Set()

  override def inputProgramVariables = Set(thisVar)

  override def outputProgramVariables = Set(thisVar)
}