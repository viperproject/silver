/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.ast
import viper.silver.ast._

/** Utility methods for triggers */
object Triggers {
  object TriggerGeneration extends GenericTriggerGenerator[Node, Type, Exp, LocalVar, QuantifiedExp, PossibleTrigger,
                                                           Old, WrappingTrigger] {

    protected def hasSubnode(root: Node, child: Node) = root.hasSubnode(child)
    protected def visit[A](root: Node)(f: PartialFunction[Node, A]) = root.visit(f)
    protected def deepCollect[A](root: Node)(f: PartialFunction[Node, A]) = root.deepCollect(f)
    protected def reduceTree[A](root: Node)(f: (Node, Seq[A]) => A) = root.reduceTree(f)
    protected def transform[N <: Node](root: N)(f: PartialFunction[Node, Node]) = root.transform(f)()
    protected def Quantification_vars(q: QuantifiedExp) = q.variables map (_.localVar)
    protected def Exp_typ(exp: Exp) = exp.typ
    protected def Trigger_exps(t: Trigger) = t.exps

    protected def Trigger(exps: Seq[Exp]) = viper.silver.ast.Trigger(exps)()
    protected def Var(id: String, typ: Type) = LocalVar(id)(typ)

    protected val wrapperMap: Map[Class[_], PossibleTrigger => WrappingTrigger] = Map(
      classOf[Old] -> (pt => OldTrigger(pt)(pt.pos,pt.info)))

    /* Note: If Add and Sub were type arguments of GenericTriggerGenerator, the latter
     *       could implement isForbiddenInTrigger already */
    protected def isForbiddenInTrigger(e: Exp) = e match {
      case _: Add | _: Sub if allowInvalidTriggers => false
      case _: ForbiddenInTrigger => true
      case _ => false
    }
  }

  object AxiomRewriter extends GenericAxiomRewriter[Type, Exp, LocalVar, Forall, EqCmp, And, Implies, Add, Sub,
                                                    Trigger, ForbiddenInTrigger] {

    private var nextUniqueId = 0

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
    protected def Quantification_vars(q: Forall) = q.variables.map(_.localVar)
    protected def Quantification_body(q: Forall) = q.exp

    protected def Quantification_copy(q: Forall, vars: Seq[LocalVar], body: Exp, triggers: Seq[Trigger]) =
      q.copy(variables = vars.map(v => LocalVarDecl(v.name, v.typ)(v.pos, v.info)), exp = body, triggers = triggers)(q.pos, q.info)

    protected def Trigger_exps(t: Trigger) = t.exps
    protected def Trigger(exps: Seq[Exp]) = ast.Trigger(exps)()

    /*
     * Abstract members - dependencies
     */

    protected val solver = SimpleArithmeticSolver

    protected def fresh(name: String, typ: Type) = {
      nextUniqueId += 1
      LocalVar(s"__rw_$name$nextUniqueId")(typ)
    }

    protected def log(message: String) {}
    protected def log(key: String, item: Any) {}
    protected def log(key: String, items: Iterable[Any]) {}
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
