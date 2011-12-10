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
  def compile(): Domain = {
    domain
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainFunction(sl: SourceLocation, name: String, p: DataTypeSequence, r: DataType) = {
    require(dataTypeSequences contains p)
    require(dataTypes contains r)
    require(domainFunctions.forall(_.name != name))
    val result = new DomainFunction(sl, name, new DomainFunctionSignature(noLocation,p,r))
    domain.pFunctions += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainPredicate(sl: SourceLocation, name: String, p: DataTypeSequence) = {
    require(domainPredicates.forall(_.name != name))
    require(dataTypeSequences contains p)
    val result = new DomainPredicate(sl, name, new DomainPredicateSignature(noLocation,p))
    domain.pPredicates += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  def addDomainAxiom(sl: SourceLocation, name: String, e: DExpression): DomainAxiom = {
    require(domain.axioms.forall(_.name != name))
    val result = new DomainAxiom(sl, name, e)
    domain.pAxioms += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  //  private[silAST] var compiled = false
  val domain: Domain = new Domain(sl, name,typeVariableNames)

  val typeParameters : Seq[TypeVariable] = domain.typeParameters
  override def typeVariables = domain.typeParameters.toSet
//  protected[silAST] val domainFunctionSignatures = new HashSet[DomainFunctionSignature]
//  protected[silAST] val domainPredicateSignatures = new HashSet[DomainPredicateSignature]

  val thisType = new NonReferenceDataType(noLocation,domain,DataTypeSequence((for (tv <- domain.typeParameters) yield new VariableType(noLocation,tv)) : _*))

  protected[silAST] override def dataTypes = programFactory.dataTypes union pDataTypes union  Set(thisType)

  protected[silAST] override def domainFactories = programFactory.domainFactories

  protected[silAST] override def domainFunctions = programFactory.domainFunctions

  override def trueExpression = programFactory.trueExpression

  override def falseExpression = programFactory.falseExpression

  protected[silAST] override def domainPredicates = programFactory.domainPredicates

}
