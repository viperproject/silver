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

  /** Annotation on a function, domain function or ADT constructor (where it also applies to the constructor's
    * destructors, once the ADT plugin has encoded them as domain functions): trigger inference treats applications of
    * it like Viper's built-in operators, i.e. they never occur in an inferred trigger term. Meant for encodings of
    * operators, such as arithmetic, comparisons and casts. Hence quantifiers that are only about such a member, e.g.
    * the axioms that define it, need explicit triggers. This concerns the triggers that Silver infers for the
    * quantifiers of a program, not the ones a backend chooses for its own quantifiers.
    */
  val NotInTriggerAnnotation = "notInTrigger"

  private val freshVariableIds = new AtomicInteger(0)

  /** The `info` of a member with [[NotInTriggerAnnotation]], for clients that build the AST directly. */
  val NotInTriggerInfo: AnnotationInfo = AnnotationInfo(Map(NotInTriggerAnnotation -> Nil))

  /** Infers triggers for quantifiers. If `program` is given, applications of members of `program` with
    * [[NotInTriggerAnnotation]] are treated like built-in operators.
    */
  class TriggerGeneration(program: Option[Program] = None)
      extends GenericTriggerGenerator[Node, Type, Exp, LocalVar, QuantifiedExp] {

    /* Shared by all generators of Viper triggers, since backends combine their results */
    override protected val nextUniqueId: AtomicInteger = freshVariableIds

    /** True iff `e` applies a member of `program` with [[NotInTriggerAnnotation]]. */
    private def isAnnotatedOperator(e: Exp): Boolean = program.exists { p =>
      val callee: Option[Infoed] = e match {
        case fa: FuncApp => p.findFunctionOptionally(fa.funcname)
        case dfa: DomainFuncApp => p.findDomainFunctionOptionally(dfa.funcname)
        case _ => None
      }
      callee.exists(_.info.getAllInfos[AnnotationInfo].exists(_.values.contains(NotInTriggerAnnotation)))
    }

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
      case e if isAnnotatedOperator(e) => false
      case _: PossibleTrigger => true
      case ee: ExtensionExp => ee.extensionIsValidTrigger()
      case Old(pt: PossibleTrigger) => !isAnnotatedOperator(pt)
      case LabelledOld(pt: PossibleTrigger, _) => !isAnnotatedOperator(pt)
      case _ => false
    }: PartialFunction[Exp, Boolean])(e)

    /* Note: If Add and Sub were type arguments of GenericTriggerGenerator, the latter
     *       could implement isForbiddenInTrigger already */
    def isForbiddenInTrigger(e: Exp) = (customIsForbiddenInTrigger orElse {
      case e if Expressions.isForbiddenInTrigger(e) => true
      case e if isAnnotatedOperator(e) => true
      case _ => false
    }: PartialFunction[Exp, Boolean])(e)

    protected def withArgs(e: Exp, args: Seq[Exp]): Exp = e match {
      case pt: PossibleTrigger => pt.withArgs(args)
      case fa: FieldAccess => fa.withArgs(args)
      case o@Old(pt: PossibleTrigger) => Old(pt.withArgs(args))(o.pos, o.info, o.errT)
      case o@LabelledOld(pt: PossibleTrigger, lbl) => LabelledOld(pt.withArgs(args), lbl)(o.pos, o.info, o.errT)
      case _ => sys.error(s"Unexpected expression $e")
    }

    protected def getArgs(e: Exp): Seq[Exp] = e match {
      case pt: PossibleTrigger => pt.getArgs
      case fa: FieldAccess => fa.getArgs
      case Old(pt: PossibleTrigger) => pt.getArgs
      case LabelledOld(pt: PossibleTrigger, _) => pt.getArgs
      case _ => sys.error(s"Unexpected expression $e")
    }

    override def getVarsInExp(e: Exp): Set[LocalVar] = {
      Expressions.getContainedVariablesExcludingLet(e)
    }

    override def modifyPossibleTriggers(relevantVars: Seq[LocalVar]) = {
      case ast.Old(_) => results =>
        results.flatten.map(t => {
          val exp = t._1
          (ast.Old(exp)(exp.pos, exp.info, exp.errT), t._2, t._3)
        })
      case ast.LabelledOld(_, l) => results =>
        results.flatten.map(t => {
          val exp = t._1
          (ast.LabelledOld(exp, l)(exp.pos, exp.info, exp.errT), t._2, t._3)
        })
      case ast.Let(v, e, _) => results =>
        /* A trigger term that uses the let-bound variable gets it replaced by its definition, which therefore must
         * not contain anything forbidden in triggers. A term that does not use the variable stays a candidate
         * whatever the variable is bound to. */
        lazy val definitionIsForbidden = e.exists { case n: Exp => isForbiddenInTrigger(n); case _ => false }
        results.flatten.flatMap(t => {
          val exp = t._1
          val varIsUsed = exp.contains(v.localVar)
          val coveredVars = t._2.filter(cv => cv != v.localVar) ++
            (if (varIsUsed) relevantVars.filter(rv => e.contains(rv)) else Seq())
          if (varIsUsed && definitionIsForbidden) {
            None
          } else {
            Some((exp.replace(v.localVar, e), coveredVars, t._3))
          }
        })
    }

    override def additionalRelevantVariables(relevantVars: Seq[LocalVar], varsToAvoid: Seq[LocalVar]): PartialFunction[Node, Seq[LocalVar]] = {
      case ast.Let(v, e, body) if body.contains(v.localVar) && relevantVars.exists(v => e.contains(v)) && varsToAvoid.forall(v => !e.contains(v)) =>
        Seq(v.localVar)
    }
  }

  /**
    * We offer two objects with different configurations.
    * If several Viper instances are to be used concurrently, code *must not* call the setCustomIsForbiddenTrigger and
    * setCustomIsPossibleTrigger methods on these objects.
    */
  object DefaultTriggerGeneration extends TriggerGeneration()

  /** A trigger generator that admits `+` and `-` in triggers, which [[AxiomRewriter]] can rewrite afterwards. */
  class TriggerGenerationWithAddAndSubtract(program: Option[Program] = None) extends TriggerGeneration(program) {
    customIsForbiddenInTrigger = {
      case _: ast.Add | _: ast.Sub => false
    }
  }

  object TriggerGenerationWithAddAndSubtract extends TriggerGenerationWithAddAndSubtract(None)

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
