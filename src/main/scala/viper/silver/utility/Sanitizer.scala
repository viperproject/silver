// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import viper.silver.ast.utility.rewriter._
import viper.silver.ast.utility.Expressions
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
  // therefore preventing clashes with other entities and preventing free variables to be
  // 'captured', i.e. mistakenly considered quantified variables.
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
  def replaceFreeVariablesInExpression[E <: Exp](expression: E, replaces: Map[LocalVar, Exp], scope: Set[String]): E = {

    def partialScope(node: Node): Set[String] = {
      node match {
        case scope: Scope => scope.scopedDecls.map(_.name).toSet
        case _ => Set()
      }
    }

    def freeVariables(exp: Exp): Set[String] = {
      Expressions.freeVariables(exp).map(_.name)
    }

    // Free variables introduced by replacement
    val introducedFreeVariables = replaces.values.flatMap(freeVariables(_)).toSet
    // TODO: check if will actually be introduced, because not all replacements should occur

    case class Context(replaces: Map[LocalVar, Exp], scope: Set[String], renames: Map[String, String] = Map())

    val result = StrategyBuilder.RewriteNodeAndContext[Node, Context]({
      case (forall: Forall, c) => {

        var scope = c.scope
        var renames = c.renames

        // Check if bound variables clash with scope
        val bounds = forall.variables.map(_.name).toSet
        val intersection = scope & bounds

        // Define how clashing bound variables will be renamed to fresh names
        intersection.foreach {
          name =>
            val freshName = fresh(name, scope ++ bounds)
            renames += ((name, freshName))
            scope += freshName
        }

        // Enforce that a variable is never both renamed and replaced
        assert((renames.keys.toSet & c.replaces.keys.map(_.name).toSet).isEmpty)

        (forall, c.copy(renames = renames, scope = scope ++ partialScope(forall)))
      }

      case (lv: LocalVarDecl, c) if c.renames.contains(lv.name) =>
        (LocalVarDecl(c.renames(lv.name), lv.typ)(lv.pos, lv.info, lv.errT), c)

      case (lv: LocalVar, c) if c.renames.contains(lv.name) =>
        (LocalVar(c.renames(lv.name), lv.typ)(lv.pos, lv.info, lv.errT), c)

      case (lv: LocalVar, c) if c.replaces.contains(lv) =>
        (c.replaces(lv), c.copy(replaces = Map()))

      case (s: Scope, c) => (s, c.copy(scope = c.scope ++ partialScope(s)))

    }, Context(replaces, scope ++ introducedFreeVariables)).execute(expression).asInstanceOf[E] //? remove cast

    result //?
  }
}
