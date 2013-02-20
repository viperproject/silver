package semper.sil.ast.utility

import semper.sil.ast._

/**
 * An implementation for visitors of the SIL AST.
 *
 * @author Stefan Heule
 */
object Visitor {

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
