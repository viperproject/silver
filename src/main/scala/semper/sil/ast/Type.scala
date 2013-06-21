package semper.sil.ast

import utility.Types

/** SIL typs. */
sealed trait Type extends Node {
  /**
   * Takes a mapping of type variables to types and substitutes all
   * occurrences of those type variables with the corresponding type.
   */
  def substitute(typVarsMap: Map[TypeVar, Type]): Type

  // At the moment, there is no subtyping in SIL.
  def isSubtype(other: Type): Boolean = {
    (this, other) match {
      case (a: DomainType, b: DomainType) =>
        a.domain == b.domain && a.typVarsMap.forall {
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
/** Type for predicates (only used internally). */
case object Pred extends BuiltInType
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
 * Type for user-defined domains.
 * @param domain The underlying domain.
 * @param typVarsMap Maps type parameters to (possibly concrete) types. May not map all type
 *                   parameters, may even be empty.
 */
case class DomainType(domain: Domain, typVarsMap: Map[TypeVar, Type]) extends Type {
  require(typVarsMap.values.forall(t => !t.isInstanceOf[TypeVar]))
  lazy val isConcrete: Boolean = {
    var res = true
    // all type variables need to be gone
    for (typVar <- domain.typVars) {
      typVarsMap.get(typVar) match {
        case None => res = false
        case Some(t) => if (!t.isConcrete) res = false
      }
    }
    res
  }

  def substitute(newTypVarsMap: Map[TypeVar, Type]): DomainType = {
    val map = domain.typVars flatMap {
      t =>
        newTypVarsMap.get(t) match {
          case Some(v) => Seq(t -> v)
          case None =>
            typVarsMap.get(t) match {
              case Some(v) => Seq(t -> v)
              case None => Nil
            }
        }
    }
    DomainType(domain, map.toMap)
  }
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
