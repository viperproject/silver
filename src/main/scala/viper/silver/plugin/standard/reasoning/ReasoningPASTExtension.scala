// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning

import viper.silver.FastMessaging
import viper.silver.ast.{Exp, ExtensionExp, LocalVar, LocalVarDecl, Position, Seqn, Stmt, Trigger}
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser.{NameAnalyser, PAssignTarget, PCall, PCallable, PDelimited, PExp, PExtender, PGrouped, PIdnRef, PIdnUseExp, PKeywordLang, PKeywordStmt, PKw, PLabel, PLocalVarDecl, PReserved, PSeqn, PStmt, PSym, PSymOp, PTrigger, PType, PTypeSubstitution, Translator, TypeChecker}

case object PObtainKeyword extends PKw("obtain") with PKeywordLang with PKeywordStmt
case object PWhereKeyword extends PKw("where") with PKeywordLang
case object PProveKeyword extends PKw("prove") with PKeywordLang with PKeywordStmt
case object PAssumingKeyword extends PKw("assuming") with PKeywordLang
case object PImpliesKeyword extends PKw("implies") with PKeywordLang
case object PInfluencedKeyword extends PKw("influenced") with PKeywordLang with PKw.PostSpec
case object PByKeyword extends PKw("by") with PKeywordLang
case object PHeapKeyword extends PKw("heap") with PKeywordLang
case object PAssumesKeyword extends PKw("assumes") with PKeywordLang
case object PNothingKeyword extends PKw("assumesNothing") with PKeywordLang with PKw.PostSpec
case object PIsLemmaKeyword extends PKw("isLemma") with PKeywordLang with PKw.PreSpec with PKw.PostSpec
case object POldCallKeyword extends PKw("oldCall") with PKeywordLang with PKeywordStmt

case class PExistentialElim(obtainKw: PReserved[PObtainKeyword.type], delimitedVarDecls: PDelimited[PLocalVarDecl, PSym.Comma], whereKw: PReserved[PWhereKeyword.type], trig: Seq[PTrigger], e: PExp)(val pos: (Position, Position)) extends PExtender with PStmt {
  lazy val varDecls: Seq[PLocalVarDecl] = delimitedVarDecls.toSeq

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    varDecls foreach (v => t.check(v.typ))
    trig foreach (_.exp.inner.toSeq foreach (tpe => t.checkTopTyped(tpe, None)))
    t.check(e, Bool)
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    ExistentialElim(
      varDecls.map { variable => LocalVarDecl(variable.idndef.name, t.ttyp(variable.typ))(t.liftPos(variable)) },
      trig.map { t1 => Trigger(t1.exp.inner.toSeq.map { t2 => t.exp(t2) })(t.liftPos(t1)) },
      t.exp(e))(t.liftPos(e))
  }
}

case class PUniversalIntro(proveKw: PReserved[PProveKeyword.type], forallKw: PKw.Forall, delimitedVarDecls: PDelimited[PLocalVarDecl, PSym.Comma], triggers: Seq[PTrigger], assumingKw: PReserved[PAssumingKeyword.type], e1: PExp, impliesKw: PReserved[PImpliesKeyword.type], e2: PExp, block: PSeqn)(val pos: (Position, Position)) extends PExtender with PStmt {
  lazy val varDecls: Seq[PLocalVarDecl] = delimitedVarDecls.toSeq

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    varDecls foreach (v => t.check(v.typ))
    triggers foreach (_.exp.inner.toSeq foreach (tpe => t.checkTopTyped(tpe, None)))
    t.check(e1, Bool)
    t.check(e2, Bool)
    t.check(block)
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    UniversalIntro(
      varDecls.map { variable => LocalVarDecl(variable.idndef.name, t.ttyp(variable.typ))(t.liftPos(variable)) },
      triggers.map { t1 => Trigger(t1.exp.inner.toSeq.map { t2 => t.exp(t2) })(t.liftPos(t1)) },
      t.exp(e1),
      t.exp(e2),
      t.stmt(block).asInstanceOf[Seqn])(t.liftPos(e1))
  }
}

trait PFlowAnnotation extends PExp with PExtender {
  val pos: (Position,Position)
}

case class PInfluencedBy(v: PFlowVar, byKw: PReserved[PByKeyword.type], groupedVarList: PGrouped[PSym.Brace, Seq[PFlowVarOrHeap]])(val pos: (Position,Position)) extends PFlowAnnotation {
  lazy val varList: Seq[PFlowVarOrHeap] = groupedVarList.inner

  override def typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {

    varList.foreach {
      case c: PVar =>
        t.checkTopTyped(c.decl, None)
      case _ =>
    }
    v match {
      case c: PVar =>
        t.checkTopTyped(c.decl, None)
      case _ =>
    }

    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    InfluencedBy(v.translate(t), varList.map { variable => variable.translate(t) })(t.liftPos(this))
  }
}

sealed trait PFlowVar extends PExtender with PExp {
  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = typecheck(t, n)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None

  def translate(t: Translator): FlowVar

  override def typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}
}

trait PFlowVarOrHeap extends PFlowVar {

  override def translate(t: Translator): FlowVarOrHeap
}

case class PHeap(heap: PReserved[PHeapKeyword.type])(val pos: (Position,Position)) extends PFlowVarOrHeap {
  override def translate(t: Translator): Heap = {
    Heap()(t.liftPos(this))
  }

  override def pretty: String = PHeapKeyword.keyword
}

case class PAssumes(assumes: PReserved[PAssumesKeyword.type])(val pos: (Position,Position)) extends PFlowVar {
  override def translate(t: Translator): Assumes = {
    Assumes()(t.liftPos(this))
  }

  override def pretty: String = PAssumesKeyword.keyword
}

case class PAssumesNothing()(val pos: (Position,Position)) extends PFlowAnnotation {
  def translate(t: Translator): AssumesNothing = {
    AssumesNothing()(t.liftPos(this))
  }

  override def pretty: String = PNothingKeyword.keyword
  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = None

  override def translateExp(t: Translator): Exp = AssumesNothing()(t.liftPos(this))

  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}
}

case class PVar(decl: PIdnUseExp)(val pos: (Position,Position)) extends PFlowVarOrHeap {
  override def translate(t: Translator): Var = {
    // due to the implementation of `t.exp`, a LocalVar should be returned
    Var(t.exp(decl).asInstanceOf[LocalVar])(t.liftPos(this))
  }

  override def pretty: String = decl.pretty
}

case class PLemmaClause()(val pos: (Position,Position)) extends PExtender with PExp {
  override def typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = typecheck(t, n)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None

  override def translateExp(t: Translator): ExtensionExp = {
    Lemma()(t.liftPos(this))
  }
}

case class POldCall(lhs: PDelimited[PExp with PAssignTarget, PSym.Comma], op: Option[PSymOp.Assign], oldCallKw: PReserved[POldCallKeyword.type], lbl: PGrouped[PSym.Bracket, Either[PKw.Lhs, PIdnRef[PLabel]]], call: PGrouped[PSym.Paren, PCall])(val pos: (Position, Position)) extends PExtender with PStmt {
  lazy val targets: Seq[PExp with PAssignTarget] = lhs.toSeq
  lazy val idnref: PIdnRef[PCallable] = call.inner.idnref
  lazy val args: Seq[PExp] = call.inner.args

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    args.foreach(a =>
      t.checkTopTyped(a, None)
    )
    targets.foreach(r =>
      t.checkTopTyped(r, None))
    targets filter {
      case _: PIdnUseExp => false
      case _ => true
    } foreach(target => t.messages ++= FastMessaging.message(target, s"expected an identifier but got $target"))
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    val labelName = lbl.inner.fold(_.rs.keyword, _.name)
    val translatedTargets = targets.map(target => t.exp(target).asInstanceOf[LocalVar]) // due to the typecheck and the implementation of `t.exp`, a LocalVar should be returned
    OldCall(idnref.name, args map t.exp, translatedTargets, labelName)(t.liftPos(this))
  }
}

/**
  * oldCall that does not assign any return parameters.
  * Note that this node is only used for parsing and is translated to `POldCall` before typechecking
  */
case class POldCallStmt(oldCallKw: PReserved[POldCallKeyword.type], lbl: PGrouped[PSym.Bracket, Either[PKw.Lhs, PIdnRef[PLabel]]], funcApp: PGrouped[PSym.Paren, PCall])(val pos: (Position, Position)) extends PExtender with PStmt {
  lazy val call: PCall = funcApp.inner
  lazy val idnref: PIdnRef[PCallable] = call.idnref
  lazy val args: Seq[PExp] = call.args

  // POldCallStmt are always transformed by `beforeResolve` in `ReasoningPlugin`. Thus, calling `typecheck` indicates a logical error
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = throw new AssertionError(s"POldCallStmt '$this' should have been transformed before typechecking")

  // we do not translate this expression but `POldCall` which is created before resolution
  override def translateStmt(t: Translator): Stmt = throw new AssertionError(s"POldCallStmt '$this' should have been transformed before typechecking")
}

/**
  * Note that this node is only used for parsing and is translated to `POldCall` before typechecking
  */
case class POldCallExp(oldCallKw: PReserved[POldCallKeyword.type], lbl: PGrouped[PSym.Bracket, Either[PKw.Lhs, PIdnRef[PLabel]]], call: PGrouped[PSym.Paren, PCall])(val pos: (Position, Position)) extends PExtender with PExp {
  lazy val idnref: PIdnRef[PCallable] = call.inner.idnref
  lazy val args: Seq[PExp] = call.inner.args

  override def typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = typecheck(t, n)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    // this node should get translated to `POldCall` but `beforeResolve` in `ReasoningPlugin` performs this translation
    // only if its parent node is a PAssign. Thus, an invocation of this function indicates that this expression occurs
    // at an unsupported location within the AST.
    // TODO check that label is valid
    Some(Seq(s"oldCalls are only supported as statements or as the right-hand side of an assignment"))
  }

  // we do not translate this expression but `POldCall` which is created before resolution
  override def translateExp(t: Translator): ExtensionExp = throw new AssertionError(s"POldCallExp '$this' should have been transformed before typechecking")
}
