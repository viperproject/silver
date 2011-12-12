package silAST.domains

import silAST.programs.{NodeFactory, ProgramFactory}
import silAST.expressions.{DExpression, DExpressionFactory}
import silAST.source.{noLocation, SourceLocation}
import silAST.types._

final class DomainFactory private[silAST](
                                           val programFactory: ProgramFactory,
                                           val sl: SourceLocation,
                                           val name: String,
                                           typeVariableNames :Seq[(SourceLocation,String)]
                                           ) extends NodeFactory with DExpressionFactory with DataTypeFactory {
  def getInstance(sequence: DataTypeSequence) : Domain

  def compile(): DomainTemplate = {
    domainTemplate
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainFunction(sl: SourceLocation, name: String, p: DataTypeSequence, r: DataType) = {
    require(p.forall(dataTypes contains _))
    require(dataTypes contains r)
    require(domainFunctions.forall(_.name != name))
    val result = new DomainFunction(sl, name, new DomainFunctionSignature(noLocation,p,r))
    domainTemplate.pFunctions += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainPredicate(sl: SourceLocation, name: String, p: DataTypeSequence) = {
    require(domainPredicates.forall(_.name != name))
    require(p.forall(dataTypes contains _))
    val result = new DomainPredicate(sl, name, new DomainPredicateSignature(noLocation,p))
    domainTemplate.pPredicates += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  def addDomainAxiom(sl: SourceLocation, name: String, e: DExpression): DomainAxiom = {
    require(domainTemplate.axioms.forall(_.name != name))
    val result = new DomainAxiom(sl, name, e)
    domainTemplate.pAxioms += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  //  private[silAST] var compiled = false
  val domainTemplate: DomainTemplate = new DomainTemplate(sl, name,typeVariableNames)

  val typeParameters : Seq[TypeVariable] = domainTemplate.typeParameters
  override def typeVariables = domainTemplate.typeParameters.toSet
//  protected[silAST] val domainFunctionSignatures = new HashSet[DomainFunctionSignature]
//  protected[silAST] val domainPredicateSignatures = new HashSet[DomainPredicateSignature]

  val thisType = new NonReferenceDataType(noLocation,domainTemplate.domain)

  protected[silAST] override def dataTypes = programFactory.dataTypes union pDataTypes union  Set(thisType)

  protected[silAST] override def domainFactories = programFactory.domainFactories

  protected[silAST] override def domainFunctions = programFactory.domainFunctions

  override def trueExpression = programFactory.trueExpression

  override def falseExpression = programFactory.falseExpression

  protected[silAST] override def domainPredicates = programFactory.domainPredicates

}
