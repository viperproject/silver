package silAST.domains

import silAST.programs.{NodeFactory, ProgramFactory}
import silAST.expressions.{DExpression, DExpressionFactory}
import silAST.source.{noLocation, SourceLocation}
import silAST.types._

final class DomainFactory private[silAST](
                                           val programFactory: ProgramFactory,

                                           val name: String,
                                           typeVariableNames :Seq[(SourceLocation,String)]
                                           )
                                         (val sourceLocation : SourceLocation)
  extends NodeFactory with DExpressionFactory with DataTypeFactory
{
  val domain = new DomainC(name,typeVariableNames)(sourceLocation)

  private[silAST] def getInstance(ta: DataTypeSequence) : Domain =
    domain.getInstance(ta)

  def compile(): Domain = {
    domain
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainFunction(name: String, p: DataTypeSequence, r: DataType)(sourceLocation : SourceLocation) = {
    require(p.forall(dataTypes contains _))
    require(dataTypes contains r)
    require(domainFunctions.forall(_.name != name))
    val result = new DomainFunctionC(name, new DomainFunctionSignature(p,r)(noLocation),domain)(sourceLocation)
    domain.pFunctions += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainPredicate(name: String, p: DataTypeSequence)(sourceLocation : SourceLocation) = {
    require(domainPredicates.forall(_.name != name))
    require(p.forall(dataTypes contains _))
    val result = new DomainPredicateC(name, new DomainPredicateSignature(p)(noLocation),domain)(sourceLocation)
    domain.pPredicates += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  def addDomainAxiom(name: String, e: DExpression)(sourceLocation : SourceLocation) : DomainAxiom = {
    require(domain.axioms.forall(_.name != name))
    val result = new DomainAxiom(name, e)(sourceLocation)
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
