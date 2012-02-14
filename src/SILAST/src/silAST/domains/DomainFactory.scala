package silAST.domains

import silAST.programs.{NodeFactory, ProgramFactory}
import silAST.expressions.{DExpression, DExpressionFactory}
import silAST.source.{noLocation, SourceLocation}
import silAST.types._

final class DomainFactory private[silAST](
                                           val programFactory: ProgramFactory,
                                           val sourceLocation : SourceLocation,
                                           val name: String,
                                           typeVariableNames :Seq[(SourceLocation,String)]
                                           ) extends NodeFactory with DExpressionFactory with DataTypeFactory 
{
  val domain = new DomainC(sourceLocation,name,typeVariableNames)

  private[silAST] def getInstance(ta: DataTypeSequence) : Domain =
    domain.getInstance(ta)

  def compile(): Domain = {
    domain
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainFunction(sourceLocation : SourceLocation, name: String, p: DataTypeSequence, r: DataType) = {
    require(p.forall(dataTypes contains _))
    require(dataTypes contains r)
    require(domainFunctions.forall(_.name != name))
    val result = new DomainFunctionC(sourceLocation, name, new DomainFunctionSignature(noLocation,p,r),domain)
    domain.pFunctions += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainPredicate(sourceLocation : SourceLocation, name: String, p: DataTypeSequence) = {
    require(domainPredicates.forall(_.name != name))
    require(p.forall(dataTypes contains _))
    val result = new DomainPredicateC(sourceLocation, name, new DomainPredicateSignature(noLocation,p),domain)
    domain.pPredicates += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  def addDomainAxiom(sourceLocation : SourceLocation, name: String, e: DExpression): DomainAxiom = {
    require(domain.axioms.forall(_.name != name))
    val result = new DomainAxiom(sourceLocation, name, e)
    domain.pAxioms += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  //  private[silAST] var compiled = false

  val typeParameters : Seq[TypeVariable] = domain.typeParameters
  override def typeVariables = domain.typeParameters.toSet

  val thisType = domain.getType

  protected[silAST] override def dataTypes = programFactory.dataTypes ++ pDataTypes  ++ Set(thisType)

  protected[silAST] override def domainFactories = programFactory.domainFactories

  protected[silAST] override def domainFunctions = programFactory.domainFunctions

  protected[silAST] override def domainPredicates = programFactory.domainPredicates

}
