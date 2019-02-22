// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast._

/** Utility methods for statements. */
object Statements {
  /** An empty statement. */
  val EmptyStmt = Seqn(Nil, Nil)()

  /**
   * Returns a list of all actual statements contained in a given statement.  That
   * is, all statements except `Seqn`, including statements in the body of loops, etc.
   */
  def children(s: Stmt): Seq[Stmt] = {
    s match {
      case While(_, _, body) => Seq(s) ++ children(body)
      case If(_, thn, els) => Seq(s) ++ children(thn) ++ children(els)
      case Seqn(ss, locals) => ss flatMap children
      case _ => List(s)
    }
  }

  /**
   * Returns a list of all undeclared local variables used in this statement.
   * If the same local variable is used with different
   * types, an exception is thrown.
   */
  def undeclLocalVars(s: Stmt): Seq[LocalVar] = {
    def extractLocal(n: Node, decls: Seq[LocalVarDecl]) = n match {
      case l: LocalVar => decls.find(_.name == l.name) match {
        case None => List(l)
        case Some(d) if d.typ != l.typ =>
          sys.error("Local variable " + l.name + " is declared with type " + d.typ + " but used with type " + l.typ + ".")
        case _ => Nil
      }
      case _ => Nil
    }
    def combineLists(s1: Seq[LocalVar], s2: Seq[LocalVar]) = {
      for (l1 <- s1; l2 <- s2) {
        if (l1.name == l2.name && l1.typ != l2.typ) {
          sys.error("Local variable " + l1.name + " is used with different types " + l1.typ + " and " + l2.typ)
        }
      }
      (s1 ++ s2).distinct
    }
    def addDecls(n: Node, decls: Seq[LocalVarDecl]) = n match {
      case QuantifiedExp(v, _) => decls ++ v
      case _ => decls
    }
    def combineResults(n: Node, decls: Seq[LocalVarDecl], localss: Seq[Seq[LocalVar]]) = {
      localss.fold(extractLocal(n, decls))(combineLists)
    }
    s.reduceWithContext(Nil, addDecls, combineResults)
  }

  /**
   * Computes all local variables that are written to in the given statement and that are declared outside of
   */
  def writtenVars(s: Stmt): Seq[LocalVar] = {
    var writtenTo = Seq[LocalVar]()

    s visit {
      case LocalVarAssign(lhs, _) => writtenTo = lhs +: writtenTo
      case MethodCall(_, _, targets) => writtenTo = writtenTo ++ targets
      case Fresh(vars) => writtenTo = writtenTo ++ vars
      case Constraining(_, body) => writtenTo = writtenTo ++ (writtenVars(body) intersect s.undeclLocalVars)
      case NewStmt(target, _) => writtenTo = target +: writtenTo
      case While(_, _, body) => writtenTo = writtenTo ++ (writtenVars(body) intersect s.undeclLocalVars)
    }

    writtenTo.distinct
  }
}
