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
  def reduceTree[N, T](n: N, subs: N => Seq[N])(f: (N, Seq[T]) => T): T = {
    val subResults = subs(n).map(reduceTree[N, T](_, subs)(f))
    f(n, subResults)
  }

  /**
   * See Node.reduceWithContext.
   */
  def reduceWithContext[N, C, R](n: N, subs: N => Seq[N])(context: C, enter: (N, C) => C, combine: (N, C, Seq[R]) => R): R = {
    val newContext = enter(n, context)
    val subResults = subs(n).map(reduceWithContext[N, C, R](_, subs)(newContext, enter, combine))
    combine(n, context, subResults)
  }

  /**
   * See Node.visit.
   */
  def visit[N, A](n: N, subs: N => Seq[N])(f: PartialFunction[N, A]) {
    if (f.isDefinedAt(n)) f(n)
    for (sub <- subs(n)) {
      visit(sub, subs)(f)
    }
  }

  /** See Node.visitWithContext. */
  def visitWithContext[N, C](n: N, subs: N => Seq[N], c: C)(f: C => PartialFunction[N, C]) {
    val fWithContext = f(c)

    val newContext =
      if (fWithContext.isDefinedAt(n)) fWithContext(n)
      else c

    for (sub <- subs(n)) {
      visitWithContext(sub, subs, newContext)(f)
    }
  }

  /** See Node.visitWithContextManually. */
  def visitWithContextManually[N, C, A](n: N, subs: N => Seq[N], c: C)(f: C => PartialFunction[N, A]) {
    val fWithContext = f(c)
    val isDefined = fWithContext.isDefinedAt(n)

    if (isDefined) {
      fWithContext(n)
    } else {
      for (sub <- subs(n)) {
        visitWithContextManually(sub, subs, c)(f)
      }
    }
  }

  /**
   * See Node.visit.
   */
  def visit[N, A](n: N, subs: N => Seq[N], f1: PartialFunction[N, A], f2: PartialFunction[N, A]) {
    if (f1.isDefinedAt(n)) f1(n)
    for (sub <- subs(n)) {
      visit(sub, subs, f1, f2)
    }
    if (f2.isDefinedAt(n)) f2(n)
  }

  /**
   * See Node.visitOpt.
   */
  def visitOpt[N](n: N, subs: N => Seq[N])(f: N => Boolean) {
    if (f(n)) {
      for (sub <- subs(n)) {
        visitOpt(sub, subs)(f)
      }
    }
  }

  /**
   * See Node.visitOpt.
   */
  def visitOpt[N, A](n: N, subs: N => Seq[N], f1: N => Boolean, f2: N => A) {
    if (f1(n)) {
      for (sub <- subs(n)) {
        visitOpt[N, A](sub, subs, f1, f2)
      }
    }
    f2(n)
  }

  /**
   * See Node.existsDefined.
   */
  def existsDefined[N, A](n: N, subs: N => Seq[N], f: PartialFunction[N, A]): Boolean = {
    visit(n, subs) {
      case e =>
        if (f.isDefinedAt(e)) return true
    }
    false
  }
}
