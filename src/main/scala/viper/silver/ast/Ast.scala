/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast

import scala.reflect.ClassTag

import pretty.FastPrettyPrinter
import utility.{Visitor, Nodes, Transformer}

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

  /** @see [[Nodes.subnodes()]] */
  def subnodes = Nodes.subnodes(this)

  /** @see [[Visitor.reduceTree()]] */
  def reduceTree[A](f: (Node, Seq[A]) => A) = Visitor.reduceTree(this, Nodes.subnodes)(f)

  /** @see [[Visitor.reduceWithContext()]] */
  def reduceWithContext[C, R](context: C, enter: (Node, C) => C, combine: (Node, C, Seq[R]) => R) = {
    Visitor.reduceWithContext(this, Nodes.subnodes)(context, enter, combine)
  }

  /** Applies the function `f` to the AST node, then visits all subnodes. */
  def foreach[A](f: Node => A) = Visitor.visit(this, Nodes.subnodes) { case a: Node => f(a) }

  /** @see [[Visitor.visit()]] */
  def visit[A](f: PartialFunction[Node, A]) {
    Visitor.visit(this, Nodes.subnodes)(f)
  }

  /** @see [[Visitor.visitWithContext()]] */
  def visitWithContext[C](c: C)(f: C => PartialFunction[Node, C]) {
    Visitor.visitWithContext(this, Nodes.subnodes, c)(f)
  }

  /** @see [[Visitor.visitWithContextManually()]] */
  def visitWithContextManually[C, A](c: C)(f: C => PartialFunction[Node, A]) {
    Visitor.visitWithContextManually(this, Nodes.subnodes, c)(f)
  }

  //** @see [[Visitor.visit()]] */
  def visit[A](f1: PartialFunction[Node, A], f2: PartialFunction[Node, A]) {
    Visitor.visit(this, Nodes.subnodes, f1, f2)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f: Node => Boolean) {
    Visitor.visitOpt(this, Nodes.subnodes)(f)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt[A](f1: Node => Boolean, f2: Node => A) {
    Visitor.visitOpt(this, Nodes.subnodes, f1, f2)
  }

  /** @see [[Visitor.existsDefined()]] */
  def existsDefined[A](f: PartialFunction[Node, A]): Boolean = Visitor.existsDefined(this, Nodes.subnodes)(f)

  /** @see [[Visitor.hasSubnode()]] */
  def hasSubnode(toFind: Node): Boolean = Visitor.hasSubnode(this, toFind, Nodes.subnodes)

  override def toString() = FastPrettyPrinter.pretty(this)

  /** @see [[viper.silver.ast.utility.Transformer.transform()]] */
  def transform(pre: PartialFunction[Node, Node] = PartialFunction.empty)
               (recursive: Node => Boolean = !pre.isDefinedAt(_),
                post: PartialFunction[Node, Node] = PartialFunction.empty)
               : this.type =

    Transformer.transform[this.type](this, pre)(recursive, post)

  def replace(original: Node, replacement: Node): this.type =
    this.transform{case `original` => replacement}()

  def replace[N <: Node: ClassTag](replacements: Map[N, Node]): this.type =
    if (replacements.isEmpty) this
    else this.transform{case t: N if replacements.contains(t) => replacements(t)}()

  /** @see [[Visitor.deepCollect()]] */
  def deepCollect[A](f: PartialFunction[Node, A]) : Seq[A] =
    Visitor.deepCollect(Seq(this), Nodes.subnodes)(f)

  /** @see [[Visitor.shallowCollect()]] */
  def shallowCollect[R](f: PartialFunction[Node, R]): Seq[R] =
    Visitor.shallowCollect(Seq(this), Nodes.subnodes)(f)

  def contains(n: Node): Boolean = this.existsDefined{
    case `n` =>
  }

  def contains[N <: Node : ClassTag]: Boolean = {
    val clazz = implicitly[ClassTag[N]].runtimeClass
    this.existsDefined{
      case n: N if clazz.isInstance(n) =>
    }
  }

  /* To be overridden in subclasses of Node. */
  def isValid: Boolean = true
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

/** An `Info` instance for labelling a quantifier as auto-triggered. */
case object AutoTriggered extends Info {
  lazy val comment = Nil
}

/** An `Info` instance for composing multiple `Info`s together */
case class ConsInfo(head: Info, tail:Info) extends Info {
  lazy val comment = head.comment ++ tail.comment
}

/** Build a `ConsInfo` instance out of two `Info`s, unless the latter is `NoInfo` (which can be dropped) */
object MakeInfoPair {
  def apply(head:Info, tail:Info) = tail match {
    case NoInfo => head
    case _ => ConsInfo(head,tail)
  }
}

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
