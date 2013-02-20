package semper.sil.ast.utility

import semper.sil.ast._

/**
 * An implementation for visitors of the SIL AST.
 *
 * @author Stefan Heule
 */
class Visitor {

  /**
   * Applies the function `f` to the AST node, then visits all subnodes.
   */
  def visit(n: Node)(f: Node => Unit) {
    f(n)
    for (sub <- n.subnodes) {
      visit(sub)(f)
    }
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes,
   * and finally calls `f2` to the AST node.
   */
  def visit(n: Node, f1: Node => Unit, f2: Node => Unit) {
    f1(n)
    for (sub <- n.subnodes) {
      visit(sub, f1, f2)
    }
    f2(n)
  }

  /**
   * Applies the function `f` to the AST node, then visits all subnodes if `f`
   * returned true.
   */
  def visitOpt(n: Node)(f: Node => Boolean) {
    if (f(n)) {
      for (sub <- n.subnodes) {
        visitOpt(sub)(f)
      }
    }
  }

  /**
   * Applies the function `f1` to the AST node, then visits all subnodes if `f1`
   * returned true, and finally calls `f2` to the AST node.
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
