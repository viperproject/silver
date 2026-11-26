// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import viper.silver.ast.utility.rewriter._
import viper.silver.parser._
import viper.silver.ast._
import viper.silver.ast.utility.Expressions

object Sanitizer {

  private def fresh(name: String, scope: Set[String]): String = {
    var number = -1
    var freshName = name
    while (scope.contains(freshName)) {
      number += 1
      freshName = s"$name$$$number"
    }
    freshName
  }

  /** This method renames bound variables when their identifiers already exist in the same scope,
    * therefore preventing name clashes with other entities and preventing free variables to be
    * 'captured', i.e., mistakenly considered bound variables. At the moment, this is not used
    * since conceptually Viper does not allow name clashes and issues a "duplicate identifier"
    * error in such cases. But this solution remains here as a suggestion of how rule number 1
    * could be implemented if name clashes were allowed.
    *
    * @param program The parse AST program to be sanitized.
    */
  def sanitizeBoundVariables(program: PProgram): PProgram = {

    def scopeAt(node: PNode): Set[String] =
      NameAnalyser().namesInScope(program, Some(node))

    case class Context(renames: Map[String, String] = Map(), freshNames: Set[String] = Set())

    StrategyBuilder.RewriteNodeAndContext[PNode, Context]({
      case (forall: PForall, c) => {

        // Check if bound variables clash with scope
        val bounds = forall.boundVars.map(_.idndef.name).toSet
        val scope = scopeAt(forall)
        val intersection = scope & bounds

        // Define how clashing variables will be renamed to fresh names
        var renames = c.renames
        var freshNames = c.freshNames

        intersection.foreach {
          name =>
            val freshName = fresh(name, scope ++ bounds ++ freshNames)
            renames += ((name, freshName))
            freshNames += freshName
        }

        (forall, Context(renames, freshNames))
      }

      case (idn@PIdnDef(name), c) if c.renames.contains(name) =>
        (PIdnDef(c.renames(name))(idn.pos), c)

      case (idn: PIdnUse, c) if c.renames.contains(idn.name) =>
        (idn.rename(c.renames(idn.name)), c)

    }, Context()).execute(program)
  }

  /** This method replaces free variables in the expression by corresponding subexpressions.
    * Variables bound (by quantifiers or lets) in the expression are not replaced, and they are
    * renamed if their identifiers clash with the scope or the free variables of the expression or
    * the replacing subexpressions, preventing these free variables from being 'captured'.
    *
    * @param expression   The expression containing free variables to be replaced.
    * @param replacements A map from free variables to expressions, specifying the required substitutions.
    * @param scope        A set of names representing the scope where the expression is located (the free
    *                     variables of the expression and of the replacing expressions are added to it).
    * @tparam E           The expression subtype.
    * @return             An expression with all expected replacements, properly sanitized.
    */
  def replaceFreeVariablesInExpression[E <: Exp](expression: E, replacements: Map[String, Exp], scope: Set[String]): E = {

    case class Context(scope: Set[String], replacements: Map[String, Exp], renaming: Map[String, String] = Map())

    // The context for the subnodes of expression: if it is a binder (a quantifier or a let), its
    // variables are renamed if they clash with the scope and hide replaced variables of the same names
    def calculateContext(expression: Exp, context: Context): Context = {
      expression match {
        case binder: Scope =>
          var scope = context.scope
          var renaming = context.renaming

          // Check if bound variables clash with scope
          val bounds = binder.scopedDecls.collect { case v: LocalVarDecl => v.name }.toSet
          val intersection = scope & bounds
          scope = scope ++ bounds

          // Plan the renaming of clashing bound variables to fresh names
          intersection.foreach {
            name =>
              val freshName = fresh(name, scope)
              renaming += ((name, freshName))
              scope += freshName
          }

          // Bound variables hide replaced variables with the same names
          val remainingReplacements = context.replacements -- bounds

          // Enforce that a variable is never both replaced and renamed
          assert((remainingReplacements.keys.toSet & renaming.keys.toSet).isEmpty)

          Context(scope, remainingReplacements, renaming)

        case _ => context
      }
    }

    def rewrite[N <: Node](node: N, context: Context): N =
      StrategyBuilder.RewriteNodeAndContext[Node, Context]({
        /* The variable of a let is not in scope in the expression it is bound to, so that expression is
         * rewritten in the outer context and the body in the let's context. The strategy does not
         * descend into lets by itself (see recurseFunc below).
         */
        case (let: Let, c) =>
          val letContext = calculateContext(let, c)
          val rewritten =
            Let(rewrite(let.variable, letContext), rewrite(let.exp, c), rewrite(let.body, letContext))(let.pos, let.info, let.errT)
          (rewritten, c)

        case (quantifier: QuantifiedExp, c) =>
          (quantifier, calculateContext(quantifier, c))

        // Rename bound variable in definition
        case (lv: LocalVarDecl, c) if c.renaming.contains(lv.name) =>
          (lv.copy(name = c.renaming(lv.name))(lv.pos, lv.info, lv.errT), c)

        // Rename bound variable in use
        case (lv: LocalVar, c) if c.renaming.contains(lv.name) =>
          (lv.copy(name = c.renaming(lv.name))(lv.pos, lv.info, lv.errT), c)

        // Replace free variable by expression
        case (lv: LocalVar, c) if c.replacements.contains(lv.name) =>
          val n = c.replacements(lv.name)
          (n, calculateContext(n, c.copy(replacements = Map(), renaming = Map())))

      }, context).recurseFunc({ case _: Let => Nil }).execute[N](node)

    // Fresh names must also avoid the free variables of the expression and of the replacing
    // expressions, which the scope given by callers need not contain
    val freeVariables = (expression +: replacements.values.toSeq).flatMap(Expressions.freeVariables(_).map(_.name))
    rewrite(expression, Context(scope ++ freeVariables, replacements))
  }
}
