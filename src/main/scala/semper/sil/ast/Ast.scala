package semper.sil.ast

import pretty.PrettyPrinter

/*

This is the SIL abstract synatx description.

Some design choices:
- Everything is either a trait, an abstract class, a case class or a case object.  Everything that we
  instantiate is a case class or case object.
- We use structural equality for everything, which is provided by default for case classes/objects.
- We use local consistency checks when nodes are created if possible, and if we know that the condition
  we check is necessary.
- val vs lazy val: We check consistency in the constructor at various nodes, which prevents us from using
  val fields in many cases due to initialization problems.  For this reason, we use lazy val.
- The AST can contain cycles, for instance for recursive methods (or functions) where the method references
  the body, which in turn contains a method call that in turn references the method.  To enable initialization,
  we make the body of the method a var field and initialize it later.  That is, during construction,
  one first needs to create all methods without a body (one can think of this as the method signature),
  and then create all the implementations.  This allows method call nodes to already reference the method
  declarations.

*/

/**
 * A common ancestor for AST nodes.  Note that this trait is not sealed, because we having all
 * AST node classes in a single file would be too tedious and difficult to manage.  However,
 * there is only a small number of subtypes of `Node`, all of which are sealed.  These are:
 * - Program
 * - Member
 * - Domain
 * - DomainMember
 * - Exp
 * - Stmt
 * - Type
 */
trait Node {
  override def toString = PrettyPrinter.pretty(this)
}

/** A trait to have additional information for nodes. */
trait Info {
  // A list of comments.
  def comment: Seq[String]
}
/** A default `Info` that is empty. */
case object NoInfo extends Info {
  lazy val comment = Nil
}
/** A simple `Info` that contains a list of comments. */
case class SimpleInfo(comment: Seq[String]) extends Info

/** A trait for nodes that have additional information. */
trait Infoed {
  def info: Info
}

/** A trait for nodes that have a position. */
trait Positioned {
  def pos: Position
}

/** A trait for nodes that have a type. */
trait Typed {
  def typ: Type

  // for convenience when checking subtyping
  def isSubtype(other: Type) = typ isSubtype other
  def isSubtype(other: Typed) = typ isSubtype other.typ
}
