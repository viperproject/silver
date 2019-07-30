// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.ast.utility.rewriter._
import viper.silver.ast.utility.rewriter.Traverse.Traverse
import viper.silver.verifier.errors.ErrorNode

/**
  * Viper specific Wrapper for the rewriting Strategies
  * Provides automatic back transformations for Node rewrites
  *
  * @param p Partial function to perform rewritings
  * @tparam C Type of context
  */
class ViperStrategy[C <: Context[Node]](p: PartialFunction[(Node, C), Node]) extends Strategy[Node, C](p) {
  override def preserveMetaData(old: Node, now: Node, directlyRewritten: Boolean): Node = {
    ViperStrategy.preserveMetaData(old, now, directlyRewritten)
  }
}

/**
  * Viper specific Wrapper for Regex Strategies
  * Provides automatic back transformations for Node to Node rewrites
  *
  * @param a The automaton generated from the regular expression
  * @param p PartialFunction that describes rewriting
  * @param d Default context
  * @tparam C Type of context
  */
class ViperRegexStrategy[C](a: TRegexAutomaton, p: PartialFunction[(Node, RegexContext[Node, C]), Node], d: PartialContextR[Node, C]) extends RegexStrategy[Node, C](a, p, d) {
  override def preserveMetaData(old: Node, now: Node, directlyRewritten: Boolean): Node = {
    ViperStrategy.preserveMetaData(old, now, directlyRewritten)
  }
}

class SlimViperRegexStrategy[C](a: TRegexAutomaton, p: PartialFunction[Node, Node]) extends SlimRegexStrategy[Node](a, p) {
  override def preserveMetaData(old: Node, now: Node, directlyRewritten: Boolean): Node = {
    ViperStrategy.preserveMetaData(old, now, directlyRewritten)
  }
}


class ViperRegexBuilder[C](acc: (C, C) => C, comp: (C, C) => C, dflt: C) extends TreeRegexBuilder[Node, C](acc, comp, dflt) {

  /**
    * Generates a TreeRegexBuilderWithMatch by adding the matching part to the mix
    *
    * @param m Regular expression
    * @return TregexBuilderWithMatch that contains regex `f`
    */
  override def &>(m: Match): ViperRegexBuilderWithMatch[C] = new ViperRegexBuilderWithMatch[C](this, m)
}


class ViperRegexBuilderWithMatch[C](v: ViperRegexBuilder[C], m: Match) extends TreeRegexBuilderWithMatch[Node, C](v, m) {

  override def |->(p: PartialFunction[(Node, RegexContext[Node, C]), Node]): ViperRegexStrategy[C] = new ViperRegexStrategy[C](m.createAutomaton(), p, new PartialContextR[Node, C](v.default, v.accumulator, v.combinator))
}


class SlimViperRegexBuilder {

  def &>(m: Match) = new SlimViperRegexBuilderWithMatch(m)
}

class SlimViperRegexBuilderWithMatch(regex: Match) {

  def |->(p: PartialFunction[Node, Node]) = new SlimViperRegexStrategy[Node](regex.createAutomaton(), p)
}

/**
  * Factory for standard rewriting configurations
  */
object ViperStrategy {

  def SlimRegex(m: Match, p: PartialFunction[Node, Node]) = {
    new SlimViperRegexBuilder &> m |-> p
  }

  def Regex[C](m: Match, p: PartialFunction[(Node, RegexContext[Node, C]), Node], default: C, acc: (C, C) => C, comb: (C, C) => C) = {
    new ViperRegexBuilder[C](acc, comb, default) &> m |-> p
  }

  /**
    * Strategy without context
    *
    * @param p Partial function to perform rewriting
    * @param t Traversion mode
    * @return ViperStrategy
    */
  def Slim(p: PartialFunction[Node, Node], t: Traverse = Traverse.TopDown) = {
    new ViperStrategy[SimpleContext[Node]](new AddArtificialContext(p)) defaultContext new NoContext[Node] traverse t
  }

  /**
    * Strategy with context about ancestors and siblings
    *
    * @param p Partial function to perform rewriting
    * @param t Traversion mode
    * @return ViperStrategy
    */
  def Ancestor(p: PartialFunction[(Node, ContextA[Node]), Node], t: Traverse = Traverse.TopDown) = {
    new ViperStrategy[ContextA[Node]](p) defaultContext new PartialContextA[Node] traverse t
  }

  /**
    * Strategy with context about ancestors, siblings and custom context
    *
    * @param p          Partial function to perform rewriting
    * @param default    Default context
    * @param updateFunc Function that specifies how to update the custom context
    * @param t          Traversion mode
    * @tparam C Type of custom context
    * @return ViperStrategy
    *
    * AS: NOTE: Its static type is a Strategy, not a ViperStrategy. It would be good practice to annotate the static types on such functions, to avoid typing surprises
    */
  def Context[C](p: PartialFunction[(Node, ContextC[Node, C]), Node], default: C, updateFunc: PartialFunction[(Node, C), C] = PartialFunction.empty, t: Traverse = Traverse.TopDown) = {
// AS: I cannot parse this style: new ViperStrategy[ContextC[Node, C]](p) defaultContext new PartialContextC[Node, C](default, updateFunc) traverse t
    new ViperStrategy[ContextC[Node, C]](p).defaultContext(new PartialContextC[Node, C](default, updateFunc)).traverse(t)
  }

  /**
    * Strategy with (only) custom context
    *
    * @param p          Partial function to perform rewriting
    * @param initialContext    Default context
    * @param updateFunc Function that specifies how to update the custom context
    * @param t          Traversion mode
    * @tparam C Type of custom context
    * @return ViperStrategy
    *
    * AS: NOTE: Its static type is a Strategy, not a ViperStrategy. It would be good practice to annotate the static types on such functions, to avoid typing surprises
    */
  def CustomContext[C](p: PartialFunction[(Node, C), Node], initialContext: C, updateFunc: PartialFunction[(Node, C), C] = PartialFunction.empty, t: Traverse = Traverse.TopDown) =
    new ViperStrategy[ContextCustom[Node, C]](
      { // rewrite partial function taking context with parent access etc. to one just taking the custom context
      case (n, generalContext) if p.isDefinedAt(n, generalContext.c) => p.apply(n, generalContext.c)
    }).defaultContext(new PartialContextCC[Node, C](initialContext, updateFunc)).traverse(t)

  /**
    * Function for automatic Error back transformation of nodes and conservation of metadata
    */
  def preserveMetaData(old: Node, now: Node, directlyRewritten: Boolean): Node = {
    old match {
      case n: ErrorNode =>
        val oldMetaData = old.getPrettyMetadata
        var newMetaData = now.getPrettyMetadata

        /* TODO: This seems like a special case, not sure if makes sense to watch out for it here */
        if ((newMetaData._1 == NoPosition) && (newMetaData._2 == NoInfo) && (newMetaData._3 == NoTrafos)) {
          newMetaData = (oldMetaData._1, oldMetaData._2, oldMetaData._3)
        }

        /* Only duplicate if old and new are actually different */
        if (old ne now) {
          /* If a node (with children) wasn't transformed itself, but was duplicated because its
           * children were transformed, then that parent node should not get an error
           * back-transformation from new to old.
           * Consider the parent node `0 < x` and a user-provided transformation that replaces `x`
           * with `foo(y)` and that adds a custom error transformation to `foo(y)` such that errors
           * are reported using `bar(y)` instead. If an error back-transformation were
           * automatically added to the parent node, then `0 < foo(y)` were mapped back (in error
           * messages) to `0 < x`, and the custom mapping from `foo(y)` to `bar(y)` would be lost.
           * Automatic error back-translations from old to new node are therefore only added to
           * nodes that have been transformed themselves (or rather, if the `directlyRewritten`
           * is true).
           */
          val newNodeTrafo = {
            if (directlyRewritten) {
              /* Attach an error transformation (in the form of a node transformation) from new to
               * old, but don't override any already attached transformations */
              Trafos(
                newMetaData._3.eTransformations,
                newMetaData._3.rTransformations,
                newMetaData._3.nTransformations.orElse(Some(n.asInstanceOf[ErrorNode])))
            } else {
              /* Keep already attached transformations (if any) */
              newMetaData._3
            }
          }
          now
        } else {
          now
        }

      case _ => now
    }
  }
}
