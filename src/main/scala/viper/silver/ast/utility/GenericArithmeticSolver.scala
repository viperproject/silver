// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import scala.annotation.tailrec
import scala.reflect.ClassTag

abstract class GenericArithmeticSolver[Type <: AnyRef,
                                       Exp <: AnyRef,
                                       Var <: Exp,
                                       Plus <: Exp : ClassTag,
                                       Minus <: Exp : ClassTag] {

  /*
   * Abstract members - type arguments
   */

  protected def Exp_type(exp: Exp): Type
  protected def Exp_deepCollect[A](node: Exp)(f: PartialFunction[Exp, A]): Seq[A]
  protected def Exp_contains(node: Exp, other: Exp): Boolean

  protected def Type_isInt(typ: Type): Boolean

  protected def Plus_apply(e1: Exp, e2: Exp): Exp
  protected def Plus_unapply(plus: Plus): (Exp, Exp)

  protected def Minus_apply(e1: Exp, e2: Exp): Exp
  protected def Minus_unapply(minus: Minus): (Exp, Exp)

  /*
   * Helpers - type arguments
   */

  object Plus {
    def apply(e1: Exp, e2: Exp) = Plus_apply(e1, e2)
    def unapply(plus: Plus) = Some(Plus_unapply(plus))
  }

  object Minus {
    def apply(e1: Exp, e2: Exp) = Minus_apply(e1, e2)
    def unapply(minus: Minus) = Some(Minus_unapply(minus))
  }

  /*
   * Actual implementation
   */

  sealed trait SolverResult {
    def readableMessage: String
  }

  case class PreSolvingError(msg: String) extends SolverResult {
    val readableMessage = msg
  }

  case class SolvingFailure(lhs: Exp, rhs: Exp, y: Var) extends SolverResult {
    val readableMessage = s"Solving for $y failed at $lhs == $rhs"
  }

  case class SolvingSuccess(y: Var, rhs: Exp) extends SolverResult {
    val readableMessage = s"Solving succeeded with $y == $rhs"
  }

  def solve(lhs: Var, rhs: Exp, y: Var): SolverResult = {
    if (!Type_isInt(Exp_type(lhs)))
      return PreSolvingError(s"LHS must be an int, but found $lhs of type ${Exp_type(lhs)}")
    if (!Type_isInt(Exp_type(rhs)))
      return PreSolvingError(s"RHS must be an int, but found $rhs of sort ${Exp_type(rhs)}")

    val rhsOccurrences = Exp_deepCollect(rhs){case `y` => y}.length

    if (lhs == y)
      PreSolvingError(s"The LHS must be different from $y")
    else if (rhsOccurrences != 1)
      PreSolvingError(s"$y must occur exactly once in the RHS, but it occurs $rhsOccurrences in $rhs")
    else {
      doSolve(lhs, rhs, y)
    }
  }

  @tailrec
  private def doSolve(lhs: Exp, rhs: Exp, y: Var): SolverResult = rhs match {
    case `y` => SolvingSuccess(y, lhs)
    case Plus(t1, t2) =>
      if (Exp_contains(t1, y)) doSolve(Minus(lhs, t2), t1, y)
      else doSolve(Minus(lhs, t1), t2, y)
    case Minus(t1, t2) =>
      if (Exp_contains(t1, y)) doSolve(Plus(lhs, t2), t1, y)
      else doSolve(Minus(t1, lhs), t2, y)
    case _ => SolvingFailure(lhs, rhs, y)
  }
}
