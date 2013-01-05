package semper.sil.ast.programs.symbols

import semper.sil.ast.programs.{ProgramFactory, NodeFactory}
import semper.sil.ast.source.noLocation
import semper.sil.ast.expressions.ExpressionFactory
import semper.sil.ast.types.referenceType


abstract class SymbolFactory[T] private[sil](
                                              private val programFactory: ProgramFactory
                                              )
  extends NodeFactory
  with ExpressionFactory {
  def compile(): T

  val thisVar = new ProgramVariable("this", referenceType)(noLocation, Nil)

  protected[sil] override def programVariables = Set(thisVar)

  protected[sil] override def fields = programFactory.fields

  protected[sil] override def functions = programFactory.functions

  protected[sil] override def predicates = programFactory.predicates

  protected[sil] override def dataTypes = programFactory.dataTypes union pDataTypes

  protected[sil] override def domainFactories = programFactory.domainFactories

  protected[sil] override def domainFunctions = programFactory.domainFunctions

  protected[sil] override def domainPredicates = programFactory.domainPredicates


}