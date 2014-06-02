package semper.sil.ast

import utility.Types

/** SIL typs. */
sealed trait Type extends Node {
  /**
   * Takes a mapping of type variables to types and substitutes all
   * occurrences of those type variables with the corresponding type.
   */
  def substitute(typVarsMap: Map[TypeVar, Type]): Type

  // At the moment, there is no user-defined subtyping in SIL.
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

  /** See [[semper.sil.ast.utility.Types.typeVariables]]. */
  lazy val typeVariables = Types.typeVariables(this)
}

/** Trait for typs build into SIL. */
sealed trait BuiltInType extends Type {
  lazy val isConcrete = true
  def substitute(typVarsMap: Map[TypeVar, Type]): Type = this
}
/** Type for integers. */
case object Int extends BuiltInType
/** Type for booleans. */
case object Bool extends BuiltInType
/** Type for permissions. */
case object Perm extends BuiltInType
/** Type for references. */
case object Ref extends BuiltInType
sealed trait InternalType extends BuiltInType
/** Type for predicates. */
case object Pred extends InternalType
/** Type for letwand-declared variables. */
case object Wand extends InternalType
/** Type for sequences */
case class SeqType(elementType: Type) extends BuiltInType {
  override lazy val isConcrete = elementType.isConcrete
  override def substitute(typVarsMap: Map[TypeVar, Type]): Type =
    SeqType(elementType.substitute(typVarsMap))
}
/** Type for sets */
case class SetType(elementType: Type) extends BuiltInType {
  override lazy val isConcrete = elementType.isConcrete
  override def substitute(typVarsMap: Map[TypeVar, Type]): Type =
    SetType(elementType.substitute(typVarsMap))
}
/** Type for multisets */
case class MultisetType(elementType: Type) extends BuiltInType {
  override lazy val isConcrete = elementType.isConcrete
  override def substitute(typVarsMap: Map[TypeVar, Type]): Type =
    MultisetType(elementType.substitute(typVarsMap))
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

  require(typVarsMap.values.forall(t => !t.isInstanceOf[TypeVar]))

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
    val unmappedTypeVars = domainTypVars filterNot typVarsMap.keys.toSet.contains
    val additionalTypeMap = (unmappedTypeVars flatMap (t => newTypVarsMap get t map (t -> _))).toMap
    val newTypeMap = typVarsMap ++ additionalTypeMap

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
}
