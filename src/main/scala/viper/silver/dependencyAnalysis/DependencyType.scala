package viper.silver.dependencyAnalysis

object AssumptionType extends Enumeration {
  type AssumptionType = Value
  val Explicit, LoopInvariant, PathCondition, Rewrite, SourceCode, DomainAxiom, Implicit, Internal, Trigger, ExplicitPostcondition, ImplicitPostcondition, ImportedPostcondition, MethodCall, FunctionBody, Precondition, Ghost, Annotation, Unknown = Value

  def fromString(s: String): Option[Value] = values.find(_.toString == s)

  def explicitAssumptionTypes: Set[AssumptionType] = Set(Explicit, ExplicitPostcondition)
  def postconditionTypes: Set[AssumptionType] = Set(ImplicitPostcondition, ExplicitPostcondition, ImportedPostcondition)
  def preconditionTypes: Set[AssumptionType] = Set(Precondition)
  def explicitAssertionTypes: Set[AssumptionType] = Set(Explicit, ImplicitPostcondition, ExplicitPostcondition)
  def internalTypes: Set[AssumptionType] = Set(Internal, Trigger) // will always be hidden from user
  def importedTypes: Set[AssumptionType] = Set(ImportedPostcondition)
  def verificationAnnotationTypes: Set[AssumptionType] = Set(FunctionBody /* TODO ake: review */, LoopInvariant, Rewrite, ExplicitPostcondition, ImplicitPostcondition, ImportedPostcondition, Precondition, Explicit, DomainAxiom, Annotation)
  def sourceCodeTypes: Set[AssumptionType] = values.diff(explicitAssumptionTypes).diff(verificationAnnotationTypes).diff(internalTypes)

  def getPostcondType(isAbstractFunction: Boolean, dependencyType: Option[DependencyType]=None, isImported: Boolean=false): AssumptionType = {
    if(isImported) return ImportedPostcondition

    dependencyType.flatMap(_.assertionType match {
      case AssumptionType.Explicit | AssumptionType.ExplicitPostcondition => Some(AssumptionType.ExplicitPostcondition)
      case AssumptionType.ImportedPostcondition => Some(AssumptionType.ImportedPostcondition)
      case AssumptionType.ImplicitPostcondition  => Some(AssumptionType.ImplicitPostcondition)
      case AssumptionType.Internal => Some(AssumptionType.Internal)
      case AssumptionType.Annotation | AssumptionType.Ghost => None
      case _ => None
    }).getOrElse(
      if(isAbstractFunction) AssumptionType.ExplicitPostcondition else AssumptionType.ImplicitPostcondition
    )
  }
}

import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType

object DependencyType {
  val SourceCode: DependencyType = make(AssumptionType.SourceCode)
  val Explicit: DependencyType = make(AssumptionType.Explicit)
  val ExplicitAssertion: DependencyType = DependencyType(AssumptionType.Internal, AssumptionType.Explicit)
  val ExplicitAssumption: DependencyType = DependencyType(AssumptionType.Explicit, AssumptionType.Implicit)
  val PathCondition: DependencyType = make(AssumptionType.PathCondition)
  val Invariant: DependencyType = make(AssumptionType.LoopInvariant)
  val Rewrite: DependencyType = make(AssumptionType.Rewrite)
  val Internal: DependencyType = make(AssumptionType.Internal)
  val Trigger: DependencyType = make(AssumptionType.Trigger)
  val MethodCall: DependencyType = make(AssumptionType.MethodCall)
  val Ghost: DependencyType = make(AssumptionType.Ghost)
  val Annotation: DependencyType = make(AssumptionType.Annotation)
  val Axiom: DependencyType = make(AssumptionType.DomainAxiom)

  def make(singleType: AssumptionType): DependencyType = DependencyType(singleType, singleType)
}

case class DependencyType(assumptionType: AssumptionType, assertionType: AssumptionType)
