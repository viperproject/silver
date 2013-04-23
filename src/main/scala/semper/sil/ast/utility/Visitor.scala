package semper.sil.ast.utility

import semper.sil.ast._

/**
 * An implementation for visitors of the SIL AST.
 *
 * @author Stefan Heule
 */
object Visitor {

  /**
   * See Node.reduceTree.
   */
  def reduceTree[T](n: Node)(f: (Node, Seq[T]) => T): T = {
    val subResults = n.subnodes.map(reduceTree[T](_)(f))
    f(n, subResults)
  }

  /**
   * See Node.reduceTree.
   */
  def reduceWithContext[C, R](n: Node)(context: C, enter: (Node, C) => C, combine: (Node, C, Seq[R]) => R): R = {
    val newContext = enter(n, context)
    val subResults = n.subnodes.map(reduceWithContext[C, R](_)(newContext, enter, combine))
    combine(n, context, subResults)
  }

  /**
   * See Node.visit.
   */
  def visit[A](n: Node)(f: PartialFunction[Node, A]) {
    if (f.isDefinedAt(n)) f(n)
    for (sub <- n.subnodes) {
      visit(sub)(f)
    }
  }

  /**
   * See Node.visit.
   */
  def visit[A](n: Node, f1: PartialFunction[Node, A], f2: PartialFunction[Node, A]) {
    if (f1.isDefinedAt(n)) f1(n)
    for (sub <- n.subnodes) {
      visit(sub, f1, f2)
    }
    if (f2.isDefinedAt(n)) f2(n)
  }

  /**
   * See Node.visitOpt.
   */
  def visitOpt(n: Node)(f: Node => Boolean) {
    if (f(n)) {
      for (sub <- n.subnodes) {
        visitOpt(sub)(f)
      }
    }
  }

  /**
   * See Node.visitOpt.
   */
  def visitOpt[A](n: Node, f1: Node => Boolean, f2: Node => A) {
    if (f1(n)) {
      for (sub <- n.subnodes) {
        visitOpt[A](sub, f1, f2)
      }
    }
    f2(n)
  }

  /**
   * See Node.exists.
   */
  def exists[A](n: Node, f: PartialFunction[Node, A]): Boolean = {
    n visit {
      case e =>
        if (f.isDefinedAt(e)) return true
    }
    false
  }
}
