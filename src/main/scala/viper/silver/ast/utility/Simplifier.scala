// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast._
import viper.silver.ast.utility.rewriter._
import viper.silver.utility.Common.Rational

/**
 * An implementation for simplifications on the Viper AST.
 */
object Simplifier {

  /**
   * Simplify `n`, in particular by making use of literals. For
   * example, `!true` is replaced by `false`. Division and modulo with divisor
   * 0 are not treated. Note that an expression with non-terminating evaluation due to endless recursion
   * might be transformed to terminating expression.
   */
  def simplify[N <: Node](n: N, assumeWelldefinedness: Boolean = false): N = {

    val simplifySingle: PartialFunction[Node, Node] = {
      // expression simplifications
      case root: Exp if root.simplified.isDefined =>
        root.simplified.get
      case root@Not(BoolLit(literal)) =>
        BoolLit(!literal)(root.pos, root.info)
      case Not(Not(single)) => single
      case root@Not(EqCmp(a, b)) => NeCmp(a, b)(root.pos, root.info)
      case root@Not(NeCmp(a, b)) => EqCmp(a, b)(root.pos, root.info)
      case root@Not(GtCmp(a, b)) => LeCmp(a, b)(root.pos, root.info)
      case root@Not(GeCmp(a, b)) => LtCmp(a, b)(root.pos, root.info)
      case root@Not(LtCmp(a, b)) => GeCmp(a, b)(root.pos, root.info)
      case root@Not(LeCmp(a, b)) => GtCmp(a, b)(root.pos, root.info)

      case And(TrueLit(), right) => right
      case And(left, TrueLit()) => left
      case root@And(FalseLit(), _) => FalseLit()(root.pos, root.info)
      case root@And(_, FalseLit()) => FalseLit()(root.pos, root.info)

      case Or(FalseLit(), right) => right
      case Or(left, FalseLit()) => left
      case root@Or(TrueLit(), _) => TrueLit()(root.pos, root.info)
      case root@Or(_, TrueLit()) => TrueLit()(root.pos, root.info)

      case root@Implies(FalseLit(), _) => TrueLit()(root.pos, root.info)
      case Implies(_, tl@TrueLit()) if assumeWelldefinedness => tl
      case Implies(TrueLit(), consequent) => consequent
      case root@Implies(FalseLit(), _) => TrueLit()(root.pos, root.info)
      case root@Implies(l1, Implies(l2, r)) => Implies(And(l1, l2)(), r)(root.pos, root.info)

      // TODO: Consider checking if Expressions.proofObligations(left) is empty (requires adding the program as parameter).
      case root@EqCmp(left, right) if assumeWelldefinedness && left == right => TrueLit()(root.pos, root.info)
      case root@EqCmp(BoolLit(left), BoolLit(right)) =>
        BoolLit(left == right)(root.pos, root.info)
      case root@EqCmp(FalseLit(), right) => Not(right)(root.pos, root.info)
      case root@EqCmp(left, FalseLit()) => Not(left)(root.pos, root.info)
      case EqCmp(TrueLit(), right) => right
      case EqCmp(left, TrueLit()) => left
      case root@EqCmp(IntLit(left), IntLit(right)) =>
        BoolLit(left == right)(root.pos, root.info)
      case root@EqCmp(NullLit(), NullLit()) => TrueLit()(root.pos, root.info)

      case root@NeCmp(BoolLit(left), BoolLit(right)) =>
        BoolLit(left != right)(root.pos, root.info)
      case NeCmp(FalseLit(), right) => right
      case NeCmp(left, FalseLit()) => left
      case root@NeCmp(TrueLit(), right) => Not(right)(root.pos, root.info)
      case root@NeCmp(left, TrueLit()) => Not(left)(root.pos, root.info)
      case root@NeCmp(IntLit(left), IntLit(right)) =>
        BoolLit(left != right)(root.pos, root.info)
      case root@NeCmp(NullLit(), NullLit()) =>
        FalseLit()(root.pos, root.info)
      case root@NeCmp(left, right) if assumeWelldefinedness && left == right => FalseLit()(root.pos, root.info)

      case CondExp(TrueLit(), ifTrue, _) => ifTrue
      case CondExp(FalseLit(), _, ifFalse) => ifFalse
      case CondExp(_, ifTrue, ifFalse) if assumeWelldefinedness && ifTrue == ifFalse =>
        ifTrue
      case root@CondExp(condition, FalseLit(), TrueLit()) =>
        Not(condition)(root.pos, root.info)
      case CondExp(condition, TrueLit(), FalseLit()) => condition
      case root@CondExp(condition, FalseLit(), ifFalse) =>
        And(Not(condition)(), ifFalse)(root.pos, root.info)
      case root@CondExp(condition, TrueLit(), ifFalse) =>
        if (ifFalse.isPure) {
          Or(condition, ifFalse)(root.pos, root.info)
        } else {
          Implies(Not(condition)(), ifFalse)(root.pos, root.info)
        }
      case root@CondExp(condition, ifTrue, FalseLit()) =>
        And(condition, ifTrue)(root.pos, root.info)
      case root@CondExp(condition, ifTrue, TrueLit()) =>
        Implies(condition, ifTrue)(root.pos, root.info)

      case root@Forall(_, _, BoolLit(literal)) =>
        BoolLit(literal)(root.pos, root.info)
      case root@Exists(_, _, BoolLit(literal)) =>
        BoolLit(literal)(root.pos, root.info)

      case root@Minus(IntLit(literal)) => IntLit(-literal)(root.pos, root.info)
      case Minus(Minus(single)) => single

      case PermMinus(PermMinus(single)) => single
      case PermMul(fst, FullPerm()) => fst
      case PermMul(FullPerm(), snd) => snd
      case root@PermMul(AnyPermLiteral(a, b), AnyPermLiteral(c, d)) =>
        val product = Rational(a, b) * Rational(c, d)
        FractionalPerm(IntLit(product.numerator)(root.pos, root.info), IntLit(product.denominator)(root.pos, root.info))(root.pos, root.info)
      case PermMul(_, np@NoPerm()) if assumeWelldefinedness => np
      case PermMul(np@NoPerm(), _) if assumeWelldefinedness => np

      case PermMul(wc@WildcardPerm(), _) if assumeWelldefinedness => wc
      case PermMul(_, wc@WildcardPerm()) if assumeWelldefinedness => wc

      case root@PermGeCmp(a, b) if assumeWelldefinedness && a == b => TrueLit()(root.pos, root.info)
      case root@PermLeCmp(a, b) if assumeWelldefinedness && a == b => TrueLit()(root.pos, root.info)
      case root@PermGtCmp(a, b) if assumeWelldefinedness && a == b => FalseLit()(root.pos, root.info)
      case root@PermLtCmp(a, b) if assumeWelldefinedness && a == b => FalseLit()(root.pos, root.info)

      case root@PermGtCmp(AnyPermLiteral(a, b), AnyPermLiteral(c, d)) =>
        BoolLit(Rational(a, b) > Rational(c, d))(root.pos, root.info)
      case root@PermGeCmp(AnyPermLiteral(a, b), AnyPermLiteral(c, d)) =>
        BoolLit(Rational(a, b) >= Rational(c, d))(root.pos, root.info)
      case root@PermLtCmp(AnyPermLiteral(a, b), AnyPermLiteral(c, d)) =>
        BoolLit(Rational(a, b) < Rational(c, d))(root.pos, root.info)
      case root@PermLeCmp(AnyPermLiteral(a, b), AnyPermLiteral(c, d)) =>
        BoolLit(Rational(a, b) <= Rational(c, d))(root.pos, root.info)
      case root@EqCmp(AnyPermLiteral(a, b), AnyPermLiteral(c, d)) =>
        BoolLit(Rational(a, b) == Rational(c, d))(root.pos, root.info)
      case root@NeCmp(AnyPermLiteral(a, b), AnyPermLiteral(c, d)) =>
        BoolLit(Rational(a, b) != Rational(c, d))(root.pos, root.info)

      case root@PermLeCmp(NoPerm(), WildcardPerm()) =>
        TrueLit()(root.pos, root.info)
      case root@NeCmp(WildcardPerm(), NoPerm()) =>
        TrueLit()(root.pos, root.info)

      case DebugPermMin(e0@AnyPermLiteral(a, b), e1@AnyPermLiteral(c, d)) =>
        if (Rational(a, b) < Rational(c, d)) {
          e0
        } else {
          e1
        }
      case root@PermSub(AnyPermLiteral(a, b), AnyPermLiteral(c, d)) =>
        val diff = Rational(a, b) - Rational(c, d)
        FractionalPerm(IntLit(diff.numerator)(root.pos, root.info), IntLit(diff.denominator)(root.pos, root.info))(root.pos, root.info)
      case root@PermAdd(AnyPermLiteral(a, b), AnyPermLiteral(c, d)) =>
        val sum = Rational(a, b) + Rational(c, d)
        FractionalPerm(IntLit(sum.numerator)(root.pos, root.info), IntLit(sum.denominator)(root.pos, root.info))(root.pos, root.info)
      case PermAdd(NoPerm(), rhs) => rhs
      case PermAdd(lhs, NoPerm()) => lhs
      case PermSub(lhs, NoPerm()) => lhs

      case root@GeCmp(IntLit(left), IntLit(right)) =>
        BoolLit(left >= right)(root.pos, root.info)
      case root@GtCmp(IntLit(left), IntLit(right)) =>
        BoolLit(left > right)(root.pos, root.info)
      case root@LeCmp(IntLit(left), IntLit(right)) =>
        BoolLit(left <= right)(root.pos, root.info)
      case root@LtCmp(IntLit(left), IntLit(right)) =>
        BoolLit(left < right)(root.pos, root.info)

      case root@Add(IntLit(left), IntLit(right)) =>
        IntLit(left + right)(root.pos, root.info)
      case root@Sub(IntLit(left), IntLit(right)) =>
        IntLit(left - right)(root.pos, root.info)
      case root@Mul(IntLit(left), IntLit(right)) =>
        IntLit(left * right)(root.pos, root.info)
      /* In the general case, Viper uses the SMT division and modulo. Scala's division is not in-sync with SMT division.
         For nonnegative dividends and divisors, all used division and modulo definitions coincide. So, in order to not
         not make any assumptions on the SMT division, division and modulo are simplified only if the dividend and divisor
         are nonnegative. Also see Carbon PR #448.
       */
      case root@Div(IntLit(left), IntLit(right)) if left >= bigIntZero && right > bigIntZero =>
        IntLit(left / right)(root.pos, root.info)
      case root@Mod(IntLit(left), IntLit(right)) if left >= bigIntZero && right > bigIntZero =>
        IntLit(left % right)(root.pos, root.info)

      // statement simplifications
      case Seqn(EmptyStmt, _) => EmptyStmt // remove empty Seqn (including unnecessary scopedDecls)
      case s@Seqn(ss, scopedDecls) if ss.contains(EmptyStmt) => // remove empty statements
        val newSS = ss.filterNot(_ == EmptyStmt)
        Seqn(newSS, scopedDecls)(s.pos, s.info, s.errT)
      case If(_, EmptyStmt, EmptyStmt) => EmptyStmt // remove empty If clause
      case If(TrueLit(), thn, _) => thn // remove trivial If conditions
      case If(FalseLit(), _, els) => els // remove trivial If conditions
    }

    val simplifyAndCache = new PartialFunction[Node, Node] {
      def apply(n: Node): Node = {
        val simplified = simplifySingle.applyOrElse(n, (nn: Node) => nn)
        n match {
          case e: Exp =>
            e.simplified = Some(simplified.asInstanceOf[Exp])
            simplified.asInstanceOf[Exp].simplified = Some(simplified.asInstanceOf[Exp])
          case _ =>
        }
        simplified
      }

      def isDefinedAt(n: Node): Boolean = n.isInstanceOf[Exp] || simplifySingle.isDefinedAt(n)
    }

    /* Always simplify children first, then treat parent. */
    StrategyBuilder.Slim[Node](simplifyAndCache, Traverse.BottomUp).recurseFunc({
      case e: Exp if e.simplified.isDefined => Nil
    }) execute n
  }

  private val bigIntZero = BigInt(0)
  private val bigIntOne = BigInt(1)

  object AnyPermLiteral {
    def unapply(p: Exp): Option[(BigInt, BigInt)] = p match {
      case FullPerm() => Some((bigIntOne, bigIntOne))
      case NoPerm() => Some((bigIntZero, bigIntOne))
      case FractionalPerm(IntLit(n), IntLit(d)) => Some((n, d))
      case _ => None
    }
  }
}
