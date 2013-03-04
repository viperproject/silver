package semper.sil.ast.utility

import semper.sil.ast._

/**
 * An implementation for visitors of the SIL AST.
 *
 * @author Stefan Heule
 */
object Visitor {
  
  /**
   * See Node.reduce.
   */
  def reduce[T](n: Node)(f: (Node, Seq[T]) => T): T = {
    val subResults = n.subnodes.map(reduce[T](_)(f))
    f(n, subResults)
  }
  
  /**
   * See Node.reduce.
   */
  def reduce[C, R](n: Node)(context: C, enter: (Node, C) => C, combine: (Node, C, Seq[R]) => R): R = {
    val newContext = enter(n, context)
    val subResults = n.subnodes.map(reduce[C, R](_)(newContext, enter, combine))
    combine(n, context, subResults)
  }

  /**
   * See Node.visit.
   */
  def visit(n: Node)(f: Node => Unit) {
    f(n)
    for (sub <- n.subnodes) {
      visit(sub)(f)
    }
  }

  /**
   * See Node.visit.
   */
  def visit(n: Node, f1: Node => Unit, f2: Node => Unit) {
    f1(n)
    for (sub <- n.subnodes) {
      visit(sub, f1, f2)
    }
    f2(n)
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
  def visitOpt(n: Node, f1: Node => Boolean, f2: Node => Unit) {
    if (f1(n)) {
      for (sub <- n.subnodes) {
        visitOpt(sub, f1, f2)
      }
    }
    f2(n)
  }
}
