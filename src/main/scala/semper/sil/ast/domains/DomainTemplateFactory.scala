package semper.sil.ast.domains

import semper.sil.ast.programs.{NodeFactory, ProgramFactory}
import semper.sil.ast.expressions.{DExpression, DExpressionFactory}
import semper.sil.ast.source.{noLocation, SourceLocation}
import semper.sil.ast.types._

final class DomainTemplateFactory private[sil](
                                                val programFactory: ProgramFactory,
                                                val name: String,
                                                typeVariableNames: Seq[(SourceLocation, String, List[String])]
                                                )
                                              (val sourceLocation: SourceLocation, comment: List[String])
  extends NodeFactory with DExpressionFactory with DataTypeFactory {
  private[sil] val pDomainTemplate: DomainTemplateC = new DomainTemplateC(name, typeVariableNames)(sourceLocation, comment)
  val domainTemplate: DomainTemplate = pDomainTemplate

  private[sil] def getInstance(ta: DataTypeSequence): DomainInstance =
    pDomainTemplate.getInstance(ta)

  def compile(): DomainTemplate = {
    pDomainTemplate
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainFunction(name: String, p: DataTypeSequence, r: DataType, sourceLocation: SourceLocation, comment: List[String] = Nil): DomainFunction = {
    require(p.forall(dataTypes contains _))
    require(dataTypes contains r)
    require(domainFunctions.forall(_.name != name))
    val result = new DomainFunctionC(name, new DomainFunctionSignature(p, r)(noLocation), pDomainTemplate)(sourceLocation, comment)
    pDomainTemplate.pFunctions += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainPredicate(name: String, p: DataTypeSequence, sourceLocation: SourceLocation, comment: List[String] = Nil): DomainPredicate = {
    require(domainPredicates.forall(_.name != name))
    require(p.forall(dataTypes contains _))
    val result = new DomainPredicateC(name, new DomainPredicateSignature(p)(noLocation), pDomainTemplate)(sourceLocation, comment)
    pDomainTemplate.pPredicates += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  def addDomainAxiom(name: String, e: DExpression, sourceLocation: SourceLocation, comment: List[String] = Nil): DomainAxiom = {
    require(pDomainTemplate.axioms.forall(_.name != name))
    val result = new DomainAxiom(name, e)(sourceLocation, comment)
    pDomainTemplate.pAxioms += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  //  private[semper.sil.ast] var compiled = false

  val typeParameters: Seq[TypeVariable] = pDomainTemplate.typeParameters

  override def typeVariables = pDomainTemplate.typeParameters.toSet

  val thisType = pDomainTemplate.getType

  protected[sil] override def dataTypes = programFactory.dataTypes ++ pDataTypes ++ Set(thisType)

  protected[sil] override def domainFactories = programFactory.domainFactories

  protected[sil] override def domainFunctions = programFactory.domainFunctions union pDomainTemplate.functions

  protected[sil] override def domainPredicates = programFactory.domainPredicates union pDomainTemplate.predicates

}
