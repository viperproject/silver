// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silver.dependencyAnalysis

import viper.silver.dependencyAnalysis.OriginType.OriginType


object OriginType {

  sealed trait OriginType {
    def asDepType(): DependencyType = DependencyType(this)
  }

  sealed trait ExplicitAssumptionType extends OriginType
  sealed trait PostconditionType extends OriginType
  sealed trait PreconditionType extends OriginType
  sealed trait ExplicitAssertionType extends OriginType
  sealed trait InternalType extends OriginType
  sealed trait ImportedType extends OriginType
  sealed trait VerificationAnnotationType extends OriginType
  sealed trait SourceCodeType extends OriginType

  case object Explicit extends OriginType with ExplicitAssumptionType with ExplicitAssertionType with VerificationAnnotationType

  case object PathCondition extends OriginType with SourceCodeType
  case object SourceCode extends OriginType with SourceCodeType
  case object MethodCall extends OriginType with SourceCodeType
  case object Ghost extends OriginType with SourceCodeType /* TODO ake: maybe should be annotation instead? */
  case object Unknown extends OriginType with SourceCodeType

  case object LoopInvariant extends OriginType with VerificationAnnotationType
  case object DomainAxiom extends OriginType with VerificationAnnotationType
  case object Rewrite extends OriginType with VerificationAnnotationType
  case object FunctionBody extends OriginType with VerificationAnnotationType /* TODO ake: maybe should be source code instead? */
  case object Annotation extends OriginType with VerificationAnnotationType

  case object Precondition extends OriginType with PreconditionType with VerificationAnnotationType
  case object ExplicitPostcondition extends OriginType with ExplicitAssumptionType with PostconditionType with ExplicitAssertionType with VerificationAnnotationType
  case object ImplicitPostcondition extends OriginType with PostconditionType with ExplicitAssertionType with VerificationAnnotationType

  case object Imported extends OriginType with ImportedType with VerificationAnnotationType

  case object Internal extends OriginType with InternalType
  case object Trigger extends OriginType with InternalType

  val values: Set[OriginType] = Set(
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
    Imported,
    MethodCall,
    FunctionBody,
    Precondition,
    Ghost,
    Annotation,
    Unknown
  )

  def fromString(s: String): Option[OriginType] = values.find(_.toString == s)

  def getPostcondType(isAbstractFunction: Boolean, dependencyType: Option[DependencyType] = None, isImported: Boolean = false): OriginType = {
    if (isImported) Imported
    else
      dependencyType.flatMap(_.assertionType match {
        case Explicit | ExplicitPostcondition => Some(ExplicitPostcondition)
        case Imported => Some(Imported)
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
  val ExplicitAssertion: DependencyType = DependencyType(OriginType.Internal, OriginType.Explicit)
  val ExplicitAssumption: DependencyType = DependencyType(OriginType.Explicit, OriginType.Annotation)

  def apply(originType: OriginType): DependencyType = new DependencyType(originType)
}

case class DependencyType(assumptionType: OriginType, assertionType: OriginType) {
  def this(originType: OriginType) = this(originType, originType)
}
