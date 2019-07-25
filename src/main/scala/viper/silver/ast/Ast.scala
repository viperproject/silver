// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast

import scala.reflect.ClassTag
import pretty.FastPrettyPrinter
import utility._
import viper.silver.ast.utility.rewriter.Traverse.Traverse
import viper.silver.ast.utility.rewriter.{Rewritable, StrategyBuilder, Traverse}
import viper.silver.verifier.errors.ErrorNode
import viper.silver.verifier.{AbstractVerificationError, ConsistencyError, ErrorReason}

/*

This is the Viper abstract syntax description.

Some design choices:
- Everything is either a trait, an abstract class, a case class or a case object.  Everything that we
  instantiate is a case class or case object.
- We use structural equality for everything, which is provided by default for case classes/objects.
- We use local consistency checks when nodes are created if possible, and if we know that the condition
  we check is necessary.
- val vs lazy val: We check consistency in the constructor at various nodes, which prevents us from using
  val fields in many cases due to initialization problems.  For this reason, we use lazy val.
- The AST can represent programs with cycles, for example to represent calls to methods. The cycles are
  handled by using the name of the corresponding program element (stored as a String), which can be looked
  up in the Program itself (e.g. findMethod). This allows AST instances to be immutable.
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
  *
  * Note that all but Program are transitive subtypes of `Node` via `Hashable`. The reason is
  * that AST node hashes may depend on the entire program, not just their sub-AST.
  */
trait Node extends Traversable[Node] with Rewritable {

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

  /** @see [[Visitor.visit()]] */
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

  def toOneLinerStr() = s"<${getClass.getSimpleName()}> ``" + (
    if (toString().indexOf("\n") != -1)
      toString().take(toString().indexOf("\n")) + "..."
    else
      toString() ) + "''"

  /** @see [[viper.silver.ast.utility.ViperStrategy]] */
  def transform(pre: PartialFunction[Node, Node] = PartialFunction.empty,
                recurse: Traverse = Traverse.Innermost)
               : this.type =

  StrategyBuilder.Slim[Node](pre, recurse) execute[this.type] (this)


  /**
    * Allows a transformation with a custom context threaded through
    *
    * @see [[viper.silver.ast.utility.ViperStrategy]] */
  def transformWithContext[C](transformation: PartialFunction[(Node,C), Node] = PartialFunction.empty,
                             initialContext: C,
                              updateFunc: PartialFunction[(Node, C), C] = PartialFunction.empty, // use this to update the context passed recursively down
                recurse: Traverse = Traverse.Innermost)
  : this.type =
    ViperStrategy.CustomContext[C](transformation, initialContext, updateFunc, recurse) execute[this.type] (this)

  def transformNodeAndContext[C](transformation: PartialFunction[(Node,C), (Node, C)],
                                 initialContext: C,
                                 recurse: Traverse = Traverse.Innermost) : this.type =
    StrategyBuilder.RewriteNodeAndContext[Node, C](transformation, initialContext, recurse).execute[this.type](this)

  def replace(original: Node, replacement: Node): this.type =
    this.transform { case `original` => replacement }

  def replace[N <: Node : ClassTag](replacements: Map[N, Node]): this.type =
    if (replacements.isEmpty) this
    else this.transform { case t: N if replacements.contains(t) => replacements(t) }

  /** @see [[Visitor.deepCollect()]] */
  def deepCollect[A](f: PartialFunction[Node, A]): Seq[A] =
  Visitor.deepCollect(Seq(this), Nodes.subnodes)(f)

  /** @see [[Visitor.shallowCollect()]] */
  def shallowCollect[R](f: PartialFunction[Node, R]): Seq[R] =
  Visitor.shallowCollect(Seq(this), Nodes.subnodes)(f)

  def contains(n: Node): Boolean = this.existsDefined {
    case `n` =>
  }

  def contains[N <: Node : ClassTag]: Boolean = {
    val clazz = implicitly[ClassTag[N]].runtimeClass
    this.existsDefined {
      case n: N if clazz.isInstance(n) =>
    }
  }

  /* To be overridden in subclasses of Node. */
  def isValid: Boolean = true

  // Get metadata with correct types
  def getPrettyMetadata: (Position, Info, ErrorTrafo) = {
    val metadata = getMetadata
    assert(metadata.size == 3, "Invalid number of metadata fields for Node:" + this)
    val pos = metadata.head match {
      case p: Position => p
      case _ => throw new AssertionError("Invalid Info of Node: " + this)
    }
    val info = metadata(1) match {
      case i: Info => i
      case _ => throw new AssertionError("Invalid Position of Node: " + this)
    }
    val errorT = metadata(2) match {
      case e: ErrorTrafo => e
      case _ => throw new AssertionError("Invalid ErrorTrafo of Node: " + this)
    }
    (pos, info, errorT)
  }

  // Default if no metadata present. Let subclasses override it if they specify position, info or Transformation
  def getMetadata: Seq[Any] = {
    Seq(NoPosition, NoInfo, NoTrafos)
  }

  //returns a list of consistency errors in the node. Only concrete classes should implement check.
  lazy val check : Seq[ConsistencyError] = Seq()
  //returns a list of consistency errors in the node as well as all its children nodes.
  lazy val checkTransitively : Seq[ConsistencyError] =
    check ++
    productIterator.flatMap{
      case n: Node => n.checkTransitively
      case s: Seq[Node @unchecked] => s.flatMap(_.checkTransitively)
      case s: Set[Node @unchecked] => s.flatMap(_.checkTransitively)
      case Some(n: Node) => n.checkTransitively
      case _ => Seq()
    }
}


/** Allow a node to have control over the error error message it causes (used in rewriter) */
trait TransformableErrors {
  /* Methods for error handling */
  def errT: ErrorTrafo

  // Rewriting strategy to transform every node back that has a back transformation specified
  private lazy val nodeTrafoStrat = StrategyBuilder.Slim[Node]({
    case n: TransformableErrors => {
      val res = transformNode(n.asInstanceOf[ErrorNode])
      res
    }
  }).repeat // Repeat because if a back-transformed node can have a back-transformation again

  // Helper function for applying the transformations
  private def foldfunc[E](tr: PartialFunction[E, E], nd: E): E = {
    if (tr.isDefinedAt(nd)) {
      tr(nd)
    } else {
      nd
    }
  }

  /** Transform error `e` back according to the transformations in backwards chronological order */
  def transformError(e: AbstractVerificationError): AbstractVerificationError = {
    val newError = errT.eTransformations.foldRight(e)(foldfunc)
    val transformedNode = nodeTrafoStrat.execute[ErrorNode](newError.offendingNode)
    newError.withNode(transformedNode).asInstanceOf[AbstractVerificationError]
  }

  /** Transform reason `e` back according to the transformations in backwards chronological order */
  def transformReason(e: ErrorReason): ErrorReason = {
    val reason = errT.rTransformations.foldRight(e)(foldfunc)
    val transformedNode = nodeTrafoStrat.execute(reason.offendingNode).asInstanceOf[ErrorNode]
    reason.withNode(transformedNode).asInstanceOf[ErrorReason]
  }

  /** Transform node `n` back according to the specified node */
  def transformNode(n: ErrorNode): ErrorNode = {
    n.errT.nTransformations.getOrElse(n)
  }
}

/** In case no error transformation is specified */
case object NoTrafos extends ErrorTrafo {
  val eTransformations = Nil
  val rTransformations = Nil
  val nTransformations = None
}

/** Class that allows generation of all transformations */
case class Trafos(error: List[PartialFunction[AbstractVerificationError, AbstractVerificationError]], reason: List[PartialFunction[ErrorReason, ErrorReason]], node: Option[ErrorNode]) extends ErrorTrafo {
  val eTransformations = error
  val rTransformations = reason
  val nTransformations = node
}

/** Create new error transformation */
case class ErrTrafo(error: PartialFunction[AbstractVerificationError, AbstractVerificationError]) extends ErrorTrafo {
  val eTransformations = List(error)
  val rTransformations = Nil
  val nTransformations = None
}

/** Create new reason transformation */
case class ReTrafo(reason: PartialFunction[ErrorReason, ErrorReason]) extends ErrorTrafo {
  val eTransformations = Nil
  val rTransformations = List(reason)
  val nTransformations = None
}

/** Create new node transformation */
case class NodeTrafo(node: ErrorNode) extends ErrorTrafo {
  val eTransformations = Nil
  val rTransformations = Nil
  val nTransformations = Some(node)
}

/** Combine two Trafos into one **/
object MakeTrafoPair {
  def apply(first: ErrorTrafo, second: ErrorTrafo) : ErrorTrafo = first match {
    case NoTrafos => second
    case _ => second match {
      case NoTrafos => first
      case _ => first + second
    }
  }
}


/** Base trait for error transformation objects */
trait ErrorTrafo {
  def eTransformations: List[PartialFunction[AbstractVerificationError, AbstractVerificationError]]

  def rTransformations: List[PartialFunction[ErrorReason, ErrorReason]]

  def nTransformations: Option[ErrorNode] // TODO: Why is this an option and not a list? Why is it OK to drop the second such value in the + definition below (if both are defined)?

  def +(t: ErrorTrafo): Trafos = {
    Trafos(eTransformations ++ t.eTransformations, rTransformations ++ t.rTransformations, if (t.nTransformations.isDefined) t.nTransformations else nTransformations)
  }
}

/** A trait to have additional information for nodes. */
trait Info {
  // A list of comments.
  def comment: Seq[String]

  // Whether the owner of this [[Info]] is cached and does not require further verification (but is still needed in the AST).
  def isCached: Boolean

  def getUniqueInfo[T <: Info:ClassTag] : Option[T] = {
    this match {
      case t:T => Some(t)
      case ConsInfo(hd,tl) => hd.getUniqueInfo[T] match {
        case Some(t) => Some(t) // assumes we don't have more than one Info entry of the desired type (somewhere nested in the ConsInfo structure)
        case None => tl.getUniqueInfo[T]
      }
      case _ => None
    }
  }
}

/** A default `Info` that is empty. */
case object NoInfo extends Info {
  lazy val comment = Nil
  lazy val isCached = false
}

/** A simple `Info` that contains a list of comments. */
case class SimpleInfo(comment: Seq[String]) extends Info {
  lazy val isCached = false
}

/** An `Info` instance for labelling a quantifier as auto-triggered. */
case object AutoTriggered extends Info {
  lazy val comment = Nil
  lazy val isCached = false
}

/** An `Info` instance for labelling a pre-verified AST node (e.g., via caching). */
case object Cached extends Info {
  lazy val comment = Nil
  lazy val isCached = true
}

/** An `Info` instance for labelling a node as synthesized. A synthesized node is one that
  * was not present in the original program that was passed to a Viper backend, such as nodes that
  * originate from an AST transformation.
  */
case object Synthesized extends Info {
  lazy val comment = Nil
  lazy val isCached = false
}

/** An `Info` instance for composing multiple `Info`s together */
case class ConsInfo(head: Info, tail: Info) extends Info {
  lazy val comment = head.comment ++ tail.comment
  lazy val isCached = head.isCached || tail.isCached
}

/** Build a `ConsInfo` instance out of two `Info`s, unless the latter is `NoInfo` (which can be dropped) */
object MakeInfoPair {
  def apply(head: Info, tail: Info) = head match {
    case NoInfo => tail
    case _ => tail match {
      case NoInfo => head
      case _ => ConsInfo(head, tail)
    }
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

/** A trait for nodes that are declarations, i.e. functions, methods, local variables etc */
trait Declaration extends Positioned {
  def name: String
}

/** A trait for nodes that define a scope. */
trait Scope {
  val scopedDecls: Seq[Declaration]

  // returns locals including those of nested scopes
  lazy val transitiveScopedDecls: Seq[Declaration] =
    scopedDecls ++
    this.asInstanceOf[Node].shallowCollect {
      case s: Scope if (s != this) => s.transitiveScopedDecls
    }.flatten
}
