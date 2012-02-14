package silAST.programs.symbols

import silAST.programs.{ProgramFactory, NodeFactory}
import silAST.source.noLocation
import silAST.expressions.ExpressionFactory
import silAST.types.referenceType


abstract class SymbolFactory[T] private[silAST](
                                                 private val programFactory: ProgramFactory
                                                 ) extends NodeFactory with ExpressionFactory {
  def compile(): T

  val thisVar = new ProgramVariable(noLocation, "this", referenceType)

  protected[silAST] override def programVariables = Set(thisVar)

  protected[silAST] override def fields = programFactory.fields

  protected[silAST] override def functions = programFactory.functions

  protected[silAST] override def predicates = programFactory.predicates

  protected[silAST] override def dataTypes = programFactory.dataTypes union pDataTypes

  protected[silAST] override def domainFactories = programFactory.domainFactories

  protected[silAST] override def domainFunctions = programFactory.domainFunctions

  protected[silAST] override def domainPredicates = programFactory.domainPredicates


}