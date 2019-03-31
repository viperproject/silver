// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

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

  /** Applies the function `f` to this node (if possible), then visits all
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

  /** A generalisation of Scala's collect, which applies not just to the list
    * of nodes ns, but also to all those transitively traversed via `subs`.
    *
    * Subnodes of nodes for which `f` is defined are traversed as well. More
    * precisely, children of a given `parent` are traversed before `f` is applied
    * to the parent itself.
    * For example, if `f` is defined for `A(_)` and for `B()`, and if `f` is
    * used to perform a deep collect over the structure `X(B(), Y(), A(B()))`,
    * then the result will be the sequence `[B(), A(B()), B()]`, where the
    * second `B()` in the sequence is the one that is nested inside `A(B())`.
    *
    * @tparam N Node type.
    * @tparam R Resulting value type.
    * @param ns List of original nodes.
    * @param subs Returns the children of a given node.
    * @param f Partial function to compute desired values.
    * @return List of collected nodes.
    */
  def deepCollect[N, R](ns: Seq[N], subs: N => Seq[N])(f: PartialFunction[N, R]): Seq[R] = {
    ns.flatMap((node: N) =>
      reduceTree(node, subs)((n: N, vs: Seq[Seq[R]]) =>
        if (f.isDefinedAt(n)) Seq(f(n)) ++ vs.flatten else vs.flatten))
  }

  /** Similar to `deepCollect`, but each node from `ns` is traversed top to
    * bottom, and the children of a parent are only visited if `f` is *not*
    * defined for the parent.
    *
    * For example, if `f` is defined for `A(_)` and for `B()`, and if `f` is
    * used to perform a shallow collect over the structure `X(B(), Y(), A(B()))`,
    * then the result will be the sequence `[B(), A(B())]` (in contrast to the
    * sequence returned by `deepCollect`).
    *
    * @tparam N Node type.
    * @tparam R Resulting value type.
    * @param ns List of original nodes.
    * @param subs Returns the children of a given node.
    * @param f Partial function to compute desired values.
    * @return List of collected nodes.
    */
  def shallowCollect[N, R](ns: Seq[N], subs: N => Seq[N])(f: PartialFunction[N, R]): Seq[R] = {
    /* The pattern `if (f isDefinedAt n) f(n) else default(n)` is inefficient,
     * see the ScalaDoc comments for PartialFunction. Instead, one should use
     * applyOrElse (and methods implemented on top of it). However, this makes
     * the code less elegant and slightly harder to read.
     *
     * The code below is conceptually equivalent to
     *   ns.flatMap((node: N) =>
     *     if (f.isDefinedAt(node)) Seq(f(node))
     *     else shallowCollect(subs(node), subs)(f))
     */

    def shallowCollect(ns: Seq[N], subs: N => Seq[N])(f: Function[N, Option[R]]): Seq[R] = {
      ns.flatMap((node: N) =>
        f(node).fold(shallowCollect(subs(node), subs)(f))(_ :: Nil))
    }

    shallowCollect(ns, subs)(f.lift)
  }

  /** Finds the first node where `f` applies and returns the result of that
    * application (if exists).
    */
  def find[N, R](n: N, subs: N => Seq[N])(f: PartialFunction[N, R]): Option[R] = {
    var result: Option[R] = None
    val fLifted = f.lift /* See ScalaDoc comments for applyOrElse for why using lift is usually more efficient */

    visit(n, subs) { case n1 =>
      result = fLifted(n1)
      if (result.nonEmpty) return result
    }

    None
  }

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
}
