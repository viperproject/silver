package semper.sil.ast

/** SIL typs. */
sealed trait Type extends Node{
  // At the moment, there is no subtyping in SIL.
  def isSubtype(other: Type) = this == other || this == Bottom
  /** Is this a concrete type (i.e. no uninstantiated type variables)? */
  def isConcrete: Boolean
}
/** Trait for typs build into SIL. */
sealed trait BuiltInType extends Type {
  lazy val isConcrete = true
}
/** Type for integers. */
case object Int extends BuiltInType
/** Type for booleans. */
case object Bool extends BuiltInType
/** Type for permissions. */
case object Perm extends BuiltInType
/** Type for references. */
case object Ref extends BuiltInType
/** Bottom type (only used internally). */
case object Bottom extends BuiltInType
/** Type for predicates (only used internally). */
case object Pred extends BuiltInType
/** Type for user-defined domains. */
case class DomainType(domain: Domain, typVarsMap: Map[TypeVar, Type]) extends Type {
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
}
/** Type variables. */
case class TypeVar(name: String) extends Type {
  lazy val isConcrete = false
}
