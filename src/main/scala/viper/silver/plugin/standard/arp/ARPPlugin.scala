// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silver.plugin.standard.arp

import fastparse._
import viper.silver.ast._
import viper.silver.ast.utility.{Expressions, ViperStrategy}
import viper.silver.parser.FastParser
import viper.silver.parser.FastParserCompanion
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.ConsistencyError
import viper.silver.verifier.errors.{InhaleFailed, LoopInvariantNotEstablished, PreconditionInCallFalse}

import scala.annotation.unused

/**
  * Adds support for abstract read permissions (ARPs), written `rd`, as introduced in
  * "Implementing Abstract Read Permissions in Viper" (Benjamin Schmid, BSc report, ETH Zurich, 2018).
  *
  * This plugin implements only the simple encoding described there: `rd` stands for some unknown positive
  * permission amount that is chosen anew for every method call and every loop, and is smaller than every
  * positive permission amount the caller holds for the locations the callee (or loop) reads with `rd`.
  * The encoding is:
  *  - Every method that uses `rd` gets an additional parameter of type Perm that replaces `rd` in its contract and
  *    body, and the precondition `none < rd && rd < write`.
  *  - At a call to such a method, a fresh variable `call_rd` is introduced, and for every `acc(e, rd)` in the callee's
  *    precondition, we assume `none < perm(e) ==> call_rd < perm(e)` (under the conditions under which the access
  *    predicate is required). `call_rd` is then passed as the additional argument. Unfolding- and asserting-expressions
  *    with `rd`, e.g., in `requires acc(P(x), rd) && unfolding acc(P(x), rd) in x.f > 0`, do not transfer permissions
  *    and need no such assumption (see [[rdConstraint]]).
  *  - Loops are handled like calls, where `rd` in the loop invariant and body refers to the loop's own amount.
  *
  * The plugin reports an error if `rd` is used in a way this encoding does not support, namely anywhere except
  * directly as the permission amount of a field or predicate access predicate (or unfolding-expression) inside a
  * method (e.g., in functions, predicates, magic wands, or arithmetic permission expressions such as `1/2 - rd`).
  *
  * The plugin is not enabled by default; use `--plugin viper.silver.plugin.standard.arp.ARPPlugin`.
  */
class ARPPlugin(@unused reporter: viper.silver.reporter.Reporter,
                @unused logger: ch.qos.logback.classic.Logger,
                @unused config: viper.silver.frontend.SilFrontendConfig,
                fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{ParserExtension, lineCol, _file}
  import FastParserCompanion.{PositionParsing, reservedKw}

  /** Parser for `rd`. */
  def rdPerm[$: P]: P[PRdPerm] = P(P(PRdKeyword) map (PRdPerm(_) _)).pos

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewKeywords(Set(PRdKeyword))
    ParserExtension.addNewExpAtStart(rdPerm(_))
    input
  }

  override def beforeVerify(input: Program): Program = {
    if (!input.exists(_.isInstanceOf[RdPerm]))
      return input

    val errorCountBefore = errors.size
    checkSupported(input)
    if (errors.size > errorCountBefore)
      return input

    val usedNames = input.deepCollect({
      case d: Declaration => d.name
      case v: LocalVar => v.name
    }).toSet
    val names = new FreshNames(usedNames)

    // The name of the additional parameter of each method that uses rd.
    val rdParams: Map[String, String] = input.methods.collect({
      case m if m.exists(_.isInstanceOf[RdPerm]) => m.name -> names.fresh(s"${m.name}_rd")
    }).toMap

    val newMethods = input.methods.map(m => rdParams.get(m.name) match {
      case None => m.copy(body = m.body.map(transformBody(input, _, None, rdParams, names)))(m.pos, m.info, m.errT)
      case Some(rdName) =>
        val rd = LocalVar(rdName, Perm)(m.pos)
        m.copy(
          formalArgs = m.formalArgs :+ LocalVarDecl(rdName, Perm)(m.pos),
          pres = rdBounds(rd) +: m.pres.map(replaceRd(_, rd)),
          posts = m.posts.map(replaceRd(_, rd)),
          body = m.body.map(transformBody(input, _, Some(rd), rdParams, names))
        )(m.pos, m.info, m.errT)
    })

    input.copy(methods = newMethods)(input.pos, input.info, input.errT)
  }

  /** Reports an error for every use of `rd` that is not supported by the simple encoding. */
  private def checkSupported(input: Program): Unit = {
    def report(r: RdPerm, msg: String): Unit =
      reportError(ConsistencyError(s"Unsupported use of abstract read permission rd: $msg", r.pos))

    def rdIn(n: Node): Seq[RdPerm] = n.deepCollect({ case r: RdPerm => r })

    input.members.foreach {
      case m: Method =>
        // rd inside magic wands (also in package and apply statements)
        m.deepCollect({ case w: MagicWand => w }).flatMap(rdIn).foreach(r =>
          report(r, "rd cannot be used inside magic wands."))
        // rd anywhere except directly as the permission amount of an access predicate
        misplacedRd(m).foreach(r =>
          report(r, "rd can only be used directly as the permission amount of an access predicate, e.g., acc(x.f, rd)."))
      case other =>
        rdIn(other).foreach(r => report(r, "rd can only be used in methods, not in functions, predicates, or domains."))
    }
  }

  private def isRd(e: Exp): Boolean = e.isInstanceOf[RdPerm]

  /** All occurrences of `rd` in `n` that are not directly the permission amount of an access predicate. */
  private def misplacedRd(n: Node): Seq[RdPerm] = n match {
    case FieldAccessPredicate(loc, Some(p)) if isRd(p) => misplacedRd(loc)
    case PredicateAccessPredicate(loc, Some(p)) if isRd(p) => misplacedRd(loc)
    case r: RdPerm => Seq(r)
    case _ => n.subnodes.flatMap(misplacedRd)
  }

  /** `none < rd && rd < write` */
  private def rdBounds(rd: LocalVar): Exp =
    And(PermLtCmp(NoPerm()(rd.pos), rd)(rd.pos), PermLtCmp(rd, FullPerm()(rd.pos))(rd.pos))(rd.pos)

  private def replaceRd[N <: Node](n: N, rd: LocalVar): N = ViperStrategy.Slim({
    case r: RdPerm => LocalVar(rd.name, Perm)(r.pos, r.info, NodeTrafo(r))
  }).execute[N](n)

  /**
    * The assumption that `rd` is smaller than every positive permission amount currently held for the locations
    * that are accessed with `rd` in `e` (under the same conditions), or None if `e` does not contain such accesses.
    * `e` is assumed to be exhaled, and contains only supported uses of `rd` (see [[checkSupported]]).
    *
    * Only access predicates that transfer permissions need such an assumption. Since the bodies of unfolding- and
    * asserting-expressions are pure, these are exactly the access predicates in the positions handled below. Access
    * predicates with `rd` in unfolding- and asserting-expressions need no assumption: since the callee's precondition
    * (or the loop invariant) is well-formed for every value of `rd`, the access predicates before them provide the
    * required permissions, and exhaling those access predicates succeeds only if the caller holds them.
    */
  private def rdConstraint(e: Exp, rd: LocalVar): Option[Exp] = {
    def rec(e: Exp): Option[Exp] = e match {
      case And(l, r) => (rec(l), rec(r)) match {
        case (Some(lc), Some(rc)) => Some(And(lc, rc)(e.pos, e.info))
        case (lc, rc) => lc.orElse(rc)
      }
      case Implies(cond, r) => rec(r).map(Implies(cond, _)(e.pos, e.info))
      case CondExp(cond, thn, els) => (rec(thn), rec(els)) match {
        case (None, None) => None
        case (tc, ec) => Some(CondExp(cond, tc.getOrElse(TrueLit()(thn.pos)), ec.getOrElse(TrueLit()(els.pos)))(e.pos, e.info))
      }
      case l@Let(v, exp, body) => rec(body).map(Let(v, exp, _)(l.pos, l.info))
      case f@Forall(vars, triggers, body) => rec(body).map(bc => {
        val q = Forall(vars, triggers, bc)(f.pos, f.info)
        if (triggers.isEmpty) q.autoTrigger else q
      })
      case InhaleExhaleExp(_, ex) => rec(ex)
      case AccessPredicate(loc, p) if isRd(p) =>
        val perm = CurrentPerm(loc)(loc.pos)
        Some(Implies(PermLtCmp(NoPerm()(loc.pos), perm)(loc.pos), PermLtCmp(rd, perm)(loc.pos))(e.pos, e.info))
      case _ => None
    }

    // conditions, let-bound expressions and locations in the constraint may contain unfolding-expressions with rd
    rec(e).map(replaceRd(_, rd))
  }

  /**
    * Replaces `rd` in `body` by `rd` (which is None if the enclosing method does not use rd) and encodes calls to
    * methods that take an rd parameter and loops.
    */
  private def transformBody(input: Program, body: Seqn, rd: Option[LocalVar], rdParams: Map[String, String], names: FreshNames): Seqn = {
    ViperStrategy.Context[Option[LocalVar]]({
      case (r: RdPerm, ctx) =>
        // Cannot happen for supported programs: rd is only used in methods that get an rd parameter.
        (LocalVar(ctx.c.get.name, Perm)(r.pos, r.info, NodeTrafo(r)), ctx)

      case (mc: MethodCall, ctx) if rdParams.contains(mc.methodName) =>
        val callee = input.findMethod(mc.methodName)
        val callRd = LocalVar(names.fresh(s"${mc.methodName}_call_rd"), Perm)(mc.pos)
        val scope = mc.args.flatMap(_.deepCollect({ case v: LocalVar => v.name })).toSet + callRd.name
        val constraints = callee.pres.flatMap(pre => {
          val instantiated = Expressions.instantiateVariables(pre, callee.formalArgs, mc.args, scope)
          rdConstraint(instantiated, callRd)
        })
        val errT = ErrTrafo({
          case InhaleFailed(_, reason, cached) => PreconditionInCallFalse(mc, reason, cached)
        })
        val call = MethodCall(mc.methodName, mc.args :+ callRd, mc.targets)(mc.pos, mc.info, mc.errT + NodeTrafo(mc))
        val encoding = Seqn(
          Inhale(rdBounds(callRd))(mc.pos, Synthesized) +:
            constraints.map(c => Inhale(c)(mc.pos, Synthesized, errT)) :+
            call,
          Seq(LocalVarDecl(callRd.name, Perm)(mc.pos))
        )(mc.pos, Synthesized)
        (ctx.noRec[Seqn](encoding), ctx)

      case (w: While, ctx) if w.exists(_.isInstanceOf[RdPerm]) =>
        val loopRd = LocalVar(names.fresh("loop_rd"), Perm)(w.pos)
        val constraints = w.invs.flatMap(inv => rdConstraint(inv, loopRd).map(c =>
          Inhale(c)(w.pos, Synthesized, ErrTrafo({
            case InhaleFailed(_, reason, cached) => LoopInvariantNotEstablished(inv, reason, cached)
          }))))
        val loop = While(
          w.cond,
          w.invs.map(replaceRd(_, loopRd)),
          transformBody(input, w.body, Some(loopRd), rdParams, names)
        )(w.pos, w.info, w.errT)
        val encoding = Seqn(
          (Inhale(rdBounds(loopRd))(w.pos, Synthesized) +: constraints) :+ loop,
          Seq(LocalVarDecl(loopRd.name, Perm)(w.pos))
        )(w.pos, Synthesized)
        (ctx.noRec[Seqn](encoding), ctx)
    }, rd).execute[Seqn](body)
  }

  /** Generates names that do not clash with each other or with the names in `used`. */
  private class FreshNames(used: Set[String]) {
    private var taken = used

    def fresh(base: String): String = {
      val name = if (!taken.contains(base)) base
                 else LazyList.from(0).map(i => s"${base}_$i").find(!taken.contains(_)).get
      taken += name
      name
    }
  }
}
