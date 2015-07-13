/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast

import utility.Types

/** Silver types. */
sealed trait Type extends Node {
  /**
   * Takes a mapping of type variables to types and substitutes all
   * occurrences of those type variables with the corresponding type.
   */
  def substitute(typVarsMap: Map[TypeVar, Type]): Type

  // At the moment, there is no user-defined subtyping in Silver.
  def isSubtype(other: Type): Boolean = {
    (this, other) match {
      case (a: DomainType, b: DomainType) =>
        a.domainName == b.domainName && a.typVarsMap.forall {
          case (tv, t1) =>
            b.typVarsMap.get(tv) match {
              case Some(t2) => t1 isSubtype t2
              case None => false
            }
        }
      case _ => this == other
    }
  }

  // Convenience method for checking subtypes
  def isSubtype(other: Typed): Boolean = isSubtype(other.typ)

  /** Is this a concrete type (i.e. no uninstantiated type variables)? */
  def isConcrete: Boolean

  /** See [[viper.silver.ast.utility.Types.typeVariables]]. */
  lazy val typeVariables = Types.typeVariables(this)
}

/** Trait for types built into Silver. */
sealed trait BuiltInType extends Type {
}

sealed trait AtomicType extends BuiltInType{
  lazy val isConcrete = true
  def substitute(typVarsMap: Map[TypeVar, Type]): Type = this
}
/** Type for integers. */
case object Int extends AtomicType
/** Type for booleans. */
case object Bool extends AtomicType
/** Type for permissions. */
case object Perm extends AtomicType
/** Type for references. */
case object Ref extends AtomicType
/** Type for predicates (only used internally). */
case object Pred extends AtomicType
/** Type for sequences */

sealed trait CollectionType extends BuiltInType {
  val elementType : Type
  override lazy val isConcrete = elementType.isConcrete
  def make(et:Type) : CollectionType
  override def substitute(typVarsMap: Map[TypeVar, Type]): Type =
    make(elementType.substitute(typVarsMap))
}
case class SeqType(override val elementType: Type) extends CollectionType{
  def make(et:Type) : SeqType = SeqType(et)
//  override def substitute(typVarsMap: Map[TypeVar, Type]): Type =
//    SeqType(elementType.substitute(typVarsMap))
}
/** Type for sets */
case class SetType(override val  elementType: Type) extends CollectionType{
//  override lazy val isConcrete = elementType.isConcrete
  def make(et:Type) : SetType = SetType(et)
//  override def substitute(typVarsMap: Map[TypeVar, Type]): Type =
//    SetType(elementType.substitute(typVarsMap))
}
/** Type for multisets */
case class MultisetType(override val  elementType: Type) extends CollectionType{
//  override lazy val isConcrete = elementType.isConcrete
  def make(et:Type) : MultisetType = MultisetType(et)
//  override def substitute(typVarsMap: Map[TypeVar, Type]): Type =
//    MultisetType(elementType.substitute(typVarsMap))
}

/**
 * Type for user-defined domains. See also the companion object below, which allows passing a Domain - this should be used in general for creation (so that domainTypVars is guaranteed to be set correctly)
 * @param domainName The name of the underlying domain.
 * @param typVarsMap Maps type parameters to (possibly concrete) types. May not map all type
 *                   parameters, may even be empty.
 */
case class DomainType (domainName: String, typVarsMap: Map[TypeVar, Type])
                      (val domainTypVars: Seq[TypeVar])
    extends Type {

  require (domainTypVars.toSet == typVarsMap.keys.toSet) 
  //  require(typVarsMap.values.forall(t => !t.isInstanceOf[TypeVar]))

  lazy val isConcrete: Boolean = {
    var res = true
    // all type variables need to be gone
    for (typVar <- domainTypVars) {
      typVarsMap.get(typVar) match {
        case None => res = false
        case Some(t) => if (!t.isConcrete) res = false
      }
    }

    res
  }

//  def getDomainTypeVars = domainTypVars

  /** Returns this domain type but adds the type variable mappings from `newTypVarsMap` to those
    * already existing in `this.typVarsMap`. Already existing mappings will '''not''' be overridden!
    * For example, if the underlying domain has a type variable `A`, if `this.typVarsMap` contains
    * `A -> Int` and if `newTypVarsMap` contains `A -> Bool`, then the result will still include
    * the mapping `A -> Int`.
    *
    * @param newTypVarsMap Additional type variable mappings.
    *
    * @return A domain type that corresponds to this domain type plus the additional type
    *         variable mappings.
    */
  def substitute(newTypVarsMap: Map[TypeVar, Type]): DomainType = {
/*    val unmappedTypeVars = domainTypVars filterNot typVarsMap.keys.toSet.contains
    val additionalTypeMap = (unmappedTypeVars flatMap (t => newTypVarsMap get t map (t -> _))).toMap
    val newTypeMap = typVarsMap ++ additionalTypeMap
  */

    assert (this.typVarsMap.keys.toSet equals this.domainTypVars.toSet)
    val newTypeMap = typVarsMap.map(kv=>kv._1 -> kv._2.substitute(newTypVarsMap))
    DomainType(domainName, newTypeMap)(domainTypVars)
  }
}

object DomainType{
  def apply(domain: Domain, typVarsMap: Map[TypeVar, Type]): DomainType =
    DomainType(domain.name, typVarsMap)(domain.typVars)
}
/** Type variables. */
case class TypeVar(name: String) extends Type {
  lazy val isConcrete = false

  def substitute(typVarsMap: Map[TypeVar, Type]): Type = {
    typVarsMap.get(this) match {
      case Some(t) => t
      case None => this
    }
  }

  //def !=(other: TypeVar) = name != other
}
