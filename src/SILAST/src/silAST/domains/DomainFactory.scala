package silAST.domains

import silAST.programs.{NodeFactory, ProgramFactory}
import silAST.source.SourceLocation
import collection.mutable.HashSet
import silAST.types.{DataTypeFactory, DataTypeSequence, DataType}
import silAST.expressions.{DExpression, DExpressionFactory}

final class DomainFactory private[silAST](
                                           val programFactory: ProgramFactory,
                                           val sl: SourceLocation,
                                           val name: String
                                           ) extends NodeFactory with DExpressionFactory with DataTypeFactory {
  def compile(): Domain = {
    domain
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainFunctionSignature(sl: SourceLocation, p: DataTypeSequence, r: DataType): DomainFunctionSignature = {
    require(dataTypeSequences contains p)
    require(dataTypes.contains(r))
    val result = new DomainFunctionSignature(sl, p, r)
    domainFunctionSignatures += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainFunction(sl: SourceLocation, name: String, s: DomainFunctionSignature) = {
    require(domainFunctions.forall(_.name != name))
    require(domainFunctionSignatures contains s)
    val result = new DomainFunction(sl, name, s)
    domain.pFunctions += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainPredicateSignature(sl: SourceLocation, p: DataTypeSequence): DomainPredicateSignature = {
    require(dataTypeSequences contains p)
    val result = new DomainPredicateSignature(sl, p)
    domainPredicateSignatures += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainPredicate(sl: SourceLocation, name: String, s: DomainPredicateSignature) = {
    require(domainPredicates.forall(_.name != name))
    require(domainPredicateSignatures.contains(s))
    val result = new DomainPredicate(sl, name, s)
    //    myDomainPredicates += name -> result
    domain.pPredicates += result
    result
  }

  //TODO: add functions/predicates to parent program

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
  val domain: Domain = new Domain(sl, name)

  protected[silAST] val domainFunctionSignatures = new HashSet[DomainFunctionSignature]
  protected[silAST] val domainPredicateSignatures = new HashSet[DomainPredicateSignature]

  protected[silAST] override def dataTypes = programFactory.dataTypes union pDataTypes

  protected[silAST] override def domainFactories = programFactory.domainFactories

  //  protected[silAST] override def dataTypeSequences //= programFactory.dataTypeSequences

  protected[silAST] override def domainFunctions = programFactory.domainFunctions

  override def trueExpression = programFactory.trueExpression

  override def falseExpression = programFactory.falseExpression

  //  protected[silAST] def myDomainPredicates = domain.pPredicates
  protected[silAST] override def domainPredicates = programFactory.domainPredicates
}
