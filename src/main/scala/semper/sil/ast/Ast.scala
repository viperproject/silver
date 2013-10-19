package semper.sil.ast

import pretty.PrettyPrinter
import utility.{ Nodes, Transformer, Visitor }

/*

This is the SIL abstract syntax description.

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
 * - LocalVarDecl
 * - Trigger
 */
trait Node extends Traversable[Node] {
  /**
   * Returns a list of all direct sub-nodes of this node. The type of nodes is
   * included in this list only for declarations (but not for expressions, for instance).
   * Furthermore, pointers to declarations are not included (e.g., the `field` of a field
   * write is not included in the result).
   */
  def subnodes = Nodes.subnodes(this)

  /**
   * Applies the function `f` to the node and the results of the subnodes.
   */
  def reduceTree[A](f: (Node, Seq[A]) => A) = Visitor.reduceTree[A](this)(f)

  /**
   * More powerful version of reduceTree that also carries a context argument through the tree.
   */
  def reduceWithContext[C, R](context: C, enter: (Node, C) => C, combine: (Node, C, Seq[R]) => R) = {
    Visitor.reduceWithContext[C, R](this)(context, enter, combine)
  }

  /**
   * Applies the function `f` to the AST node, then visits all subnodes.
   */
  def foreach[A](f: Node => A) = Visitor.visit(this) { case a: Node => f(a) }

  /**
   * Applies the function `f` to the AST node, then visits all subnodes.
   */
  def visit[A](f: PartialFunction[Node, A]) {
    Visitor.visit(this)(f)
  }

  /**
   * Applies the function `f` to the AST node, then visits all subodes. Also carries a context
   * down the tree that can be updated by `f`.
   *
   * @tparam C Context type.
   * @param c Initial context.
   * @param f Visitor function.
   */
  def visitWithContext[C](c: C)(f: C => PartialFunction[Node, C]) {
    Visitor.visitWithContext(this, c)(f)
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes,
   * and finally calls `f2` to the AST node.
   */
  def visit[A](f1: PartialFunction[Node, A], f2: PartialFunction[Node, A]) {
    Visitor.visit(this, f1, f2)
  }

  /**
   * Applies the function `f` to the AST node, then visits all subnodes if `f`
   * returned true.
   */
  def visitOpt(f: Node => Boolean) {
    Visitor.visitOpt(this)(f)
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes if `f1`
   * returned true, and finally calls `f2` to the AST node.
   */
  def visitOpt[A](f1: Node => Boolean, f2: Node => A) {
    Visitor.visitOpt(this, f1, f2)
  }

  /**
   * Checks whether the partial function is defined for any of the subnodes.  This is
   * useful to check if the node contains a subnode of a given type, or with a
   * certain property.
   */
  def existsDefined[A](f: PartialFunction[Node, A]): Boolean = Visitor.existsDefined(this, f)

  override def toString = PrettyPrinter.pretty(this)

  /**
   * Transforms the tree rooted at this node using the partial function `pre`,
   * recursing on the subnodes and finally using the partial function `post`.
   *
   * The previous node is replaced by applying `pre` and `post`, respectively,
   * if and only if these partial functions are defined there. The functions
   * `pre` and `post` must produce nodes that are valid in the given context.
   * For instance, they cannot replace an integer literal by a Boolean literal.
   *
   * @param pre       Partial function used before the recursion.
   *                  Default: partial function with the empty domain.
   * @param recursive Given the original node, should the children of the node
   *                  transformed with `pre` be transformed recursively? `pre`,
   *                  `recursive` and `post` are kept the same during each
   *                  recursion.
   *                  Default: recurse if and only if `pre` is not defined
   *                  there.
   * @param post      Partial function used after the recursion.
   *                  Default: partial function with the empty domain.
   *
   * @return Transformed tree.
   */
  def transform(pre: PartialFunction[Node, Node] = PartialFunction.empty)(
    recursive: Node => Boolean = !pre.isDefinedAt(_),
    post: PartialFunction[Node, Node] = PartialFunction.empty): this.type =
    Transformer.transform[this.type](this, pre)(recursive, post)
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
