/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

/** Implements various visiting strategies that can be applied to trees. */
object Visitor {

  /* Visit a tree for side-effects */

  /** Applies the function `f` to the AST node, then visits all subnodes. */
  def visit[N, A](n: N, subs: N => Seq[N])(f: PartialFunction[N, A]) {
    if (f.isDefinedAt(n)) f(n)

    for (sub <- subs(n)) {
      visit(sub, subs)(f)
    }
  }

  /** Applies the function `f` to this node node (if possible), then visits all
    * subnodes. Also carries a context down the tree that can be updated by `f`.
    *
    * @tparam C Context type.
    * @param c Initial context.
    * @param f Visitor function.
    */
  def visitWithContext[N, C](n: N, subs: N => Seq[N], c: C)(f: C => PartialFunction[N, C]) {
    val fWithContext = f(c)

    val newContext =
      if (fWithContext.isDefinedAt(n)) fWithContext(n)
      else c

    for (sub <- subs(n)) {
      visitWithContext(sub, subs, newContext)(f)
    }
  }

  /** Applies the function `f` to this node (if possible). Subnodes are only
    * visited if `f` is not applicable. If subnodes need to be visited when `f`
    * is applicable then `f` has to descend manually.
    * Also carries a context down the tree that can be updated by `f`.
    *
    * @tparam C Context type.
    * @tparam A Return type of the visitor function (irrelevant since return
    *           value is discarded).
    * @param c Initial context.
    * @param f Visitor function.
    */
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

  /** Applies the function `f1` to this node, then visits all subnodes,
    * and finally applies `f2` to this node.
    */
  def visit[N, A](n: N, subs: N => Seq[N], f1: PartialFunction[N, A], f2: PartialFunction[N, A]) {
    if (f1.isDefinedAt(n)) f1(n)

    for (sub <- subs(n)) {
      visit(sub, subs, f1, f2)
    }

    if (f2.isDefinedAt(n)) f2(n)
  }

  /** Applies the function `f` to this node, then visits all subnodes if `f`
    * returned true.
    */
  def visitOpt[N](n: N, subs: N => Seq[N])(f: N => Boolean) {
    if (f(n)) {
      for (sub <- subs(n)) {
        visitOpt(sub, subs)(f)
      }
    }
  }

  /** Applies the function `f1` to this node node, then visits all subnodes
    * if `f1` returned true, and finally applies `f2` to this node.
    */
  def visitOpt[N, A](n: N, subs: N => Seq[N], f1: N => Boolean, f2: N => A) {
    if (f1(n)) {
      for (sub <- subs(n)) {
        visitOpt[N, A](sub, subs, f1, f2)
      }
    }

    f2(n)
  }

  /* Query a tree */

  /** Checks whether the partial function is defined for any of the subnodes.
    * This is useful to check if the node contains a subnode of a given type,
    * or with a certain property.
    */
  def existsDefined[N, A](n: N, subs: N => Seq[N])(f: PartialFunction[N, A]): Boolean = {
    visit(n, subs) {
      case e => if (f.isDefinedAt(e)) return true
    }

    false
  }

  /** Checks whether the parameter is a proper subnode of this node */
  def hasSubnode[N](parent: N, toFind: N, subs: N => Seq[N]): Boolean =
    this.existsDefined(parent, subs){ case found if found == toFind && found != parent => }

  /* Reduce a tree to a value */

  /** Applies the function `f` to the node and the results of the subnodes. */
  def reduceTree[N, R](n: N, subs: N => Seq[N])(f: (N, Seq[R]) => R): R = {
    val subResults = subs(n).map(reduceTree(_, subs)(f))

    f(n, subResults)
  }

  /** More powerful version of `reduceTree` that also carries a context argument
    * through the tree.
    */
  def reduceWithContext[N, C, R]
                       (n: N, subs: N => Seq[N])
                       (context: C, enter: (N, C) => C, combine: (N, C, Seq[R]) => R)
                       : R = {

    val newContext = enter(n, context)
    val subResults = subs(n).map(reduceWithContext(_, subs)(newContext, enter, combine))

    combine(n, context, subResults)
  }

  /** A generalisation of Scala's collect, which applies not just to the list
    * of nodes ns, but also to all those transitively traversed via `subs`.
    *
    * @tparam N Node type.
    * @tparam R Resulting value type.
    * @param ns List of original nodes.
    * @param f Partial function to compute desired values.
    */
  def deepCollect[N, R](ns: Seq[N], subs: N => Seq[N])(f: PartialFunction[N, R]) : Seq[R] = {
    ns.flatMap((node: N) =>
      reduceTree(node, subs)((n: N, vs: Seq[Seq[R]]) =>
        if (f.isDefinedAt(n)) Seq(f(n)) ++ vs.flatten else vs.flatten))
  }
}
