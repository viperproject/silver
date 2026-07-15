// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silver.dependencyAnalysis

import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType


object AssumptionType {

  sealed trait AssumptionType {
    def asDepType(): DependencyType = DependencyType(this)
  }

  sealed trait ExplicitAssumptionType extends AssumptionType
  sealed trait PostconditionType extends AssumptionType
  sealed trait PreconditionType extends AssumptionType
  sealed trait ExplicitAssertionType extends AssumptionType
  sealed trait InternalType extends AssumptionType
  sealed trait ImportedType extends AssumptionType
  sealed trait VerificationAnnotationType extends AssumptionType
  sealed trait SourceCodeType extends AssumptionType

  case object Explicit extends AssumptionType with ExplicitAssumptionType with ExplicitAssertionType with VerificationAnnotationType

  case object PathCondition extends AssumptionType with SourceCodeType
  case object SourceCode extends AssumptionType with SourceCodeType
  case object MethodCall extends AssumptionType with SourceCodeType
  case object Ghost extends AssumptionType with SourceCodeType /* TODO ake: maybe should be annotation instead? */
  case object Unknown extends AssumptionType with SourceCodeType

  case object LoopInvariant extends AssumptionType with VerificationAnnotationType
  case object DomainAxiom extends AssumptionType with VerificationAnnotationType
  case object Rewrite extends AssumptionType with VerificationAnnotationType
  case object FunctionBody extends AssumptionType with VerificationAnnotationType /* TODO ake: maybe should be source code instead? */
  case object Annotation extends AssumptionType with VerificationAnnotationType

  case object Precondition extends AssumptionType with PreconditionType with VerificationAnnotationType
  case object ExplicitPostcondition extends AssumptionType with ExplicitAssumptionType with PostconditionType with ExplicitAssertionType with VerificationAnnotationType
  case object ImplicitPostcondition extends AssumptionType with PostconditionType with ExplicitAssertionType with VerificationAnnotationType
  case object ImportedPostcondition extends AssumptionType with PostconditionType with ImportedType with VerificationAnnotationType

  case object Internal extends AssumptionType with InternalType
  case object Trigger extends AssumptionType with InternalType

  val values: Set[AssumptionType] = Set(
    Explicit,
    LoopInvariant,
    PathCondition,
    Rewrite,
    SourceCode,
    DomainAxiom,
    Internal,
    Trigger,
    ExplicitPostcondition,
    ImplicitPostcondition,
    ImportedPostcondition,
    MethodCall,
    FunctionBody,
    Precondition,
    Ghost,
    Annotation,
    Unknown
  )

  def fromString(s: String): Option[AssumptionType] = values.find(_.toString == s)

  def getPostcondType(isAbstractFunction: Boolean, dependencyType: Option[DependencyType] = None, isImported: Boolean = false): AssumptionType = {
    if (isImported) return ImportedPostcondition

    dependencyType.flatMap(_.assertionType match {
      case Explicit | ExplicitPostcondition => Some(ExplicitPostcondition)
      case ImportedPostcondition => Some(ImportedPostcondition)
      case ImplicitPostcondition => Some(ImplicitPostcondition)
      case Internal => Some(Internal)
      case Annotation | Ghost => None
      case _ => None
    }).getOrElse(
      if (isAbstractFunction) ExplicitPostcondition else ImplicitPostcondition
    )
  }
}

object DependencyType {
  val ExplicitAssertion: DependencyType = DependencyType(AssumptionType.Internal, AssumptionType.Explicit)
  val ExplicitAssumption: DependencyType = DependencyType(AssumptionType.Explicit, AssumptionType.Annotation)

  def apply(assumptionType: AssumptionType): DependencyType = new DependencyType(assumptionType)
}

case class DependencyType(assumptionType: AssumptionType, assertionType: AssumptionType) {
  def this(assumptionType: AssumptionType) = this(assumptionType, assumptionType)
}
