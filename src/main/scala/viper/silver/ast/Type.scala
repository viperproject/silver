// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast

import scala.collection.breakOut
import utility.Types
import viper.silver.verifier.ConsistencyError

/** Silver types. */
trait Type extends Hashable {
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
      case (Wand, Bool) => true
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
/** Type used for internal nodes (e.g. typing predicate accesses) - should not be
  * the type of any expression whose value is meaningful in the translation.
  */
case object InternalType extends AtomicType
/** Type for letwand-declared variables. */
case object Wand extends AtomicType

//Base type for collections and domain types
sealed trait GenericType extends Type
{
  type Substitution = Map[TypeVar, Type]
  type MyType <: GenericType
  def genericName : String
  def typVarsMap: Substitution
  def typeParameters : Seq[TypeVar]
  def typeArguments : Seq[Type] = typeParameters.map(typVarsMap(_))
  def substitute(s: Substitution) : MyType =
    make(s)
  protected def make(s : Substitution) : MyType

  override def isConcrete = typVarsMap.values.forall(_.isConcrete)
}

/** Base type for collections */
sealed trait CollectionType extends BuiltInType with GenericType {
  val elementType : Type
  val typeParameter = TypeVar("X")
  override type MyType <: CollectionType
  override val typeParameters = Seq(typeParameter)
  override val typVarsMap: Map[TypeVar, Type] = Map((typeParameter,elementType))

//  override lazy val isConcrete = elementType.isConcrete

  protected def make(s : Substitution) : MyType = {
    make(typVarsMap(typeParameter).substitute(s))
  }
  protected def make(et:Type) : MyType
}
/** Type for sequences */
sealed case class SeqType(override val elementType: Type) extends CollectionType{
  override type MyType = SeqType
  override def make(et:Type) : MyType = SeqType(et)
  override val genericName = "Seq"
//  override def substitute(typVarsMap: Map[TypeVar, Type]): Tpe =
//    SeqType(elementType.substitute(typVarsMap))y
}
/** Type for sets */
sealed case class SetType(override val  elementType: Type) extends CollectionType{
//  override lazy val isConcrete = elementType.isConcrete
  override type MyType = SetType
  override def make(et:Type) : MyType = SetType(et)
  override val genericName = "Set"
//  override def substitute(typVarsMap: Map[TypeVar, Type]): Type =
//    SetType(elementType.substitute(typVarsMap))
}
/** Type for multisets */
sealed case class MultisetType(override val  elementType: Type) extends CollectionType{
//  override lazy val isConcrete = elementType.isConcrete
  override type MyType = MultisetType
  override def make(et:Type) : MyType = MultisetType(et)
  override val genericName = "MultiSet"
  //  override def substitute(typVarsMap: Map[TypeVar, Type]): Type =
//    MultisetType(elementType.substitute(typVarsMap))
}

/** Type for user-defined domains. See also the companion object below, which allows passing a
  * Domain - this should be used in general for creation (so that domainTypVars is guaranteed to
  * be set correctly)
  *
  * @param domainName The name of the underlying domain.
  * @param partialTypVarsMap Maps type parameters to (possibly concrete) types. May not map all
  *                          type parameters, may even be empty.
  */
sealed case class DomainType(domainName: String, partialTypVarsMap: Map[TypeVar, Type])
                            (val typeParameters: Seq[TypeVar])
    extends GenericType {

  /* Map each type parameter `A` to `partialTypVarsMap(A)`, if defined, otherwise to `A` itself.
   * `typVarsMap` thus contains a mapping for each type parameter.
   */
  val typVarsMap: Map[TypeVar, Type] =
    typeParameters.map(tp => tp -> partialTypVarsMap.getOrElse(tp, tp))(breakOut)

  override lazy val check =
    if(!(typeParameters.toSet == typVarsMap.keys.toSet)) Seq(ConsistencyError(s"${typeParameters.toSet} doesn't equal ${typVarsMap.keys.toSet}", NoPosition)) else Seq()

  override val genericName = domainName
  override type MyType = DomainType

  /** Returns this domain type but adds the type variable mappings from `newTypVarsMap` to those
    * already existing in `this.typVarsMap`. Already existing mappings will '''not''' be overridden!
    * For example, if the underlying domain has a type variable `A`, if `this.typVarsMap` contains
    * `A -> Int` and if `newTypVarsMap` contains `A -> Bool`, then the result will still include
    * the mapping `A -> Int`.
    *
    * @param newTypVarsMap Additional type variable mappings.
    * @return A domain type that corresponds to this domain type plus the additional type
    *         variable mappings.
    */
  override def make(newTypVarsMap: Map[TypeVar, Type]): MyType = {
    assert (this.typVarsMap.keys.toSet equals this.typeParameters.toSet)
    val newTypeMap = typVarsMap.map(kv=>kv._1 -> kv._2.substitute(newTypVarsMap))
    DomainType(domainName, newTypeMap)(typeParameters)
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
    typVarsMap.getOrElse(this,this)/* match {
      case Some(t) => t
      case None => this
    }                                */
  }

  //def !=(other: TypeVar) = name != other
}

trait ExtensionType extends Type{
  def getAstType: Type = ???
}
