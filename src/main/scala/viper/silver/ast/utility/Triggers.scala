// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast
import viper.silver.ast._

import java.util.concurrent.atomic.AtomicInteger

/** Utility methods for triggers */
object Triggers {

  class TriggerGeneration extends GenericTriggerGenerator[Node, Type, Exp, LocalVar, QuantifiedExp] {
    protected def hasSubnode(root: Node, child: Node) = root.hasSubnode(child)
    protected def visit[A](root: Node)(f: PartialFunction[Node, A]) = root.visit(f)
    protected def deepCollect[A](root: Node)(f: PartialFunction[Node, A]) = root.deepCollect(f)
    protected def reduceTree[A](root: Node)(f: (Node, Seq[A]) => A) = root.reduceTree(f)
    protected def transform[N <: Node](root: N)(f: PartialFunction[Node, Node]) = root.transform(f)
    protected def Quantification_vars(q: QuantifiedExp) = q.variables map (_.localVar)
    protected def Exp_typ(exp: Exp) = exp.typ
    protected def Trigger_exps(t: Trigger) = t.exps

    protected def Trigger(exps: Seq[Exp]) = viper.silver.ast.Trigger(exps)()
    protected def Var(id: String, typ: Type) = LocalVar(id, typ)()

    /* True iff the given node is a possible trigger */
    protected def isPossibleTrigger(e: Exp): Boolean = (customIsPossibleTrigger orElse {
      case _: PossibleTrigger => true
      case Old(_: PossibleTrigger) => true
      case LabelledOld(_: PossibleTrigger, _) => true
      case _ => false
    }: PartialFunction[Exp, Boolean])(e)

    /* Note: If Add and Sub were type arguments of GenericTriggerGenerator, the latter
     *       could implement isForbiddenInTrigger already */
    def isForbiddenInTrigger(e: Exp) = (customIsForbiddenInTrigger orElse {
      case _: ForbiddenInTrigger => true
      case _ => false
    }: PartialFunction[Exp, Boolean])(e)

    protected def withArgs(e: Exp, args: Seq[Exp]): Exp = e match {
      case pt: PossibleTrigger => pt.withArgs(args)
      case fa: FieldAccess => fa.withArgs(args)
      case _ => sys.error(s"Unexpected expression $e")
    }

    protected def getArgs(e: Exp): Seq[Exp] = e match {
      case pt: PossibleTrigger => pt.getArgs
      case fa: FieldAccess => fa.getArgs
      case _ => sys.error(s"Unexpected expression $e")
    }
  }

  /**
    * We offer two objects with different configurations.
    * If several Viper instances are to be used concurrently, code *must not* call the setCustomIsForbiddenTrigger and
    * setCustomIsPossibleTrigger methods on these objects.
    */
  object DefaultTriggerGeneration extends TriggerGeneration

  object TriggerGenerationWithAddAndSubtract extends TriggerGeneration {
    customIsForbiddenInTrigger = {
      case _: ast.Add | _: ast.Sub => false
    }
  }

  object AxiomRewriter extends GenericAxiomRewriter[Type, Exp, LocalVar, QuantifiedExp, EqCmp, And, Implies, Add, Sub,
                                                    Trigger] {

    private val nextUniqueId = new AtomicInteger(0)

    /*
     * Abstract members - type arguments
     */

    protected def Exp_type(exp: Exp) = exp.typ

    protected def Exp_shallowCollect[R](node: Exp)(f: PartialFunction[Exp, R]) =
      Visitor.shallowCollect[Exp, R](Seq(node), Expressions.subExps)(f)

    protected def Exp_contains(node: Exp, other: Exp) = node.contains(other)
    protected def Exp_replace(node: Exp, original: Exp, replacement: Exp) = node.replace(original, replacement)

    protected def Eq(e1: Exp, e2: Exp) = EqCmp(e1, e2)()
    protected def And(es: Seq[Exp]) = es.foldLeft(TrueLit()(): Exp){case (acc, e) => ast.And(acc, e)()}
    protected def Implies(e1: Exp, e2: Exp) = ast.Implies(e1, e2)()

    protected def Var_id(v: LocalVar) = v.name

    protected def Quantification_triggers(q: Forall) = q.triggers
    protected def Quantification_vars(q: QuantifiedExp) = q.variables.map(_.localVar)
    protected def Quantification_body(q: QuantifiedExp) = q.exp

    protected def Quantification_copy(q: QuantifiedExp, vars: Seq[LocalVar], body: Exp, triggers: Seq[Trigger]) = q match {
      case f: Forall => f.copy(variables = vars.map(v => LocalVarDecl(v.name, v.typ)(v.pos, v.info, v.errT)), exp = body, triggers = triggers)(q.pos, q.info, q.errT)
      case e: Exists => e.copy(variables = vars.map(v => LocalVarDecl(v.name, v.typ)(v.pos, v.info, v.errT)), exp = body, triggers = triggers)(q.pos, q.info, q.errT)
      case _ => sys.error(s"Unexpected expression $q")
    }


    protected def Trigger_exps(t: Trigger) = t.exps
    protected def Trigger(exps: Seq[Exp]) = ast.Trigger(exps)()

    /* True iff the given node is not allowed in triggers */
    protected def isForbiddenInTrigger(e: Exp): Boolean = DefaultTriggerGeneration.isForbiddenInTrigger(e)

    /*
     * Abstract members - dependencies
     */

    protected val solver = SimpleArithmeticSolver

    protected def fresh(name: String, typ: Type) = {
      LocalVar(s"__rw_$name${nextUniqueId.incrementAndGet()}", typ)()
    }

    protected def log(message: String): Unit = {}
    protected def log(key: String, item: Any): Unit = {}
    protected def log(key: String, items: Iterable[Any]): Unit = {}
  }

  object SimpleArithmeticSolver extends GenericArithmeticSolver[Type, Exp, LocalVar, Add, Sub] {

    /*
     * Abstract members - type arguments
     */

    protected def Exp_type(exp: Exp) = exp.typ

    protected def Exp_deepCollect[R](node: Exp)(f: PartialFunction[Exp, R]) =
      Visitor.deepCollect[Exp, R](Seq(node), Expressions.subExps)(f)

    protected def Exp_contains(node: Exp, other: Exp) = node.contains(other)

    protected def Type_isInt(typ: Type) = typ == ast.Int

    protected def Plus_apply(e1: Exp, e2: Exp) = Add(e1, e2)()
    protected def Plus_unapply(add: Add) = (add.left, add.right)

    protected def Minus_apply(e1: Exp, e2: Exp) = Sub(e1, e2)()
    protected def Minus_unapply(sub: Sub) = (sub.left, sub.right)
  }
}
