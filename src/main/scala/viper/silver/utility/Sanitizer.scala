// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import viper.silver.ast.utility.rewriter._
import viper.silver.parser._
import viper.silver.ast._

//? TODO: Considering copying metadata
//? TODO: Consider trafo to preserve original names for type checker errors
//? TODO: Consider refactoring to reuse fresh name calculator
//? TODO: Consider a stateful implementation of fresh name calculator to save time

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

  // This method renames bound variables when their identifiers already exist in the same scope,
  // therefore preventing name clashes with other entities and preventing free variables to be
  // 'captured', i.e., mistakenly considered bound variables. At the moment, this is not used
  // since conceptually Viper does not allow name clashes and issues a "duplicate identifier"
  // error in such cases. But this solution remains here as a suggestion of how rule number 1
  // could be implemented if name clashes were allowed.
  def sanitizeBoundVariables(program: PProgram): PProgram = {

    def scopeAt(node: PNode): Set[String] =
      NameAnalyser().namesInScope(program, Some(node))

    case class Context(renames: Map[String, String] = Map(), freshNames: Set[String] = Set())

    StrategyBuilder.RewriteNodeAndContext[PNode, Context]({
      case (forall: PForall, c) => {

        // Check if bound variables clash with scope
        val bounds = forall.vars.map(_.idndef.name).toSet
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

      case (PIdnDef(name), c) if c.renames.contains(name) =>
        (PIdnDef(c.renames(name)), c)

      case (PIdnUse(name), c) if c.renames.contains(name) =>
        (PIdnUse(c.renames(name)), c)

    }, Context()).execute(program)
  }

  // This method replaces free variables in the expression by corresponding subexpressions.
  // If bound variables exist and their identifiers clash with the new free variables or scope,
  // then the bound variables are renamed, preventing the new free variables from being 'captured'.
  def replaceFreeVariablesInExpression[E <: Exp](expression: E, replacements: Map[LocalVar, Exp], scope: Set[String]): E = {

    case class Context(scope: Set[String], replacements: Map[LocalVar, Exp], renaming: Map[String, String] = Map())

    val result = StrategyBuilder.RewriteNodeAndContext[Node, Context]({
      case (forall: Forall, c) => {

        var scope = c.scope
        var renaming = c.renaming

        // Check if bound variables clash with scope
        val bounds = forall.variables.map(_.name).toSet
        val intersection = scope & bounds
        scope = scope ++ bounds

        // Plan the renaming of clashing bound variables to fresh names
        intersection.foreach {
          name =>
            val freshName = fresh(name, scope)
            renaming += ((name, freshName))
            scope += freshName
        }

        // Enforce that a variable is never both replaced and renamed
        assert((c.replacements.keys.map(_.name).toSet & renaming.keys.toSet).isEmpty)

        (forall, c.copy(scope = scope, renaming = renaming))
      }

      // Rename bound variable in definition
      case (lv: LocalVarDecl, c) if c.renaming.contains(lv.name) =>
        (LocalVarDecl(c.renaming(lv.name), lv.typ)(lv.pos, lv.info, lv.errT), c)

      // Rename bound variable in use
      case (lv: LocalVar, c) if c.renaming.contains(lv.name) =>
        (LocalVar(c.renaming(lv.name), lv.typ)(lv.pos, lv.info, lv.errT), c)

      // Replace free variable by expression
      case (lv: LocalVar, c) if c.replacements.contains(lv) =>
        (c.replacements(lv), c.copy(replacements = Map(), renaming = Map()))

    }, Context(scope, replacements)).execute(expression).asInstanceOf[E] //? Remove cast

    result //? Remove 'result' as it is here just for debugging
  }
}
