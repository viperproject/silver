package viper.silver.plugin.standard.reasoning

import viper.silver.ast.{ExtensionExp, Label, LocalVar, LocalVarDecl, Position, Seqn, Stmt, Trigger}
import viper.silver.parser.TypeHelper.Bool
import viper.silver.parser.{NameAnalyser, PAssignTarget, PCall, PCallable, PDelimited, PExp, PExtender, PGrouped, PIdnRef, PKeywordLang, PKeywordStmt, PKw, PLabel, PLocalVarDecl, PNode, PReserved, PSeqn, PStmt, PSym, PSymOp, PTrigger, PType, PTypeSubstitution, Translator, TypeChecker}

case object PObtainKeyword extends PKw("obtain") with PKeywordLang with PKeywordStmt
case object PWhereKeyword extends PKw("where") with PKeywordLang
case object PProveKeyword extends PKw("prove") with PKeywordLang with PKeywordStmt
case object PAssumingKeyword extends PKw("assuming") with PKeywordLang
case object PImpliesKeyword extends PKw("implies") with PKeywordLang
case object PInfluencedKeyword extends PKw("influenced") with PKeywordLang with PKw.PostSpec
case object PByKeyword extends PKw("by") with PKeywordLang
case object PHeapKeyword extends PKw("heap") with PKeywordLang
case object PIsLemmaKeyword extends PKw("isLemma") with PKeywordLang with PKw.AnySpec
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

case class PFlowAnnotation(v: PFlowVar, byKw: PReserved[PByKeyword.type], groupedVarList: PGrouped[PSym.Brace, Seq[PFlowVar]])(val pos: (Position,Position)) extends PExtender with PExp {
  lazy val varList: Seq[PFlowVar] = groupedVarList.inner

  override def typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  //from here new
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
    FlowAnnotation(v.translate(t), varList.map { variable => variable.translate(t) })(t.liftPos(this))
  }
}

sealed trait PFlowVar extends PNode {
  def translate(t:Translator): FlowVar
}

case class PHeap(heap: PReserved[PHeapKeyword.type])(val pos: (Position,Position)) extends PFlowVar {
  override def translate(t:Translator): Heap = {
    Heap()(t.liftPos(this))
  }

  override def pretty: String = PHeapKeyword.keyword
}

case class PVar(decl:PExp)(val pos: (Position,Position)) extends PFlowVar {
  override def translate(t:Translator): Var = {
    Var(t.exp(decl))(t.liftPos(this))
  }

  override def pretty: String = decl.pretty
}

case class PLemmaClause()(val pos: (Position,Position)) extends PExtender with PExp {
  override def typeSubstitutions: Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    None
  }

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
    None
  }

  override def translateStmt(t: Translator): Stmt = {
    val labelName = lbl.inner.fold(_.rs.keyword, _.name)
    OldCall(idnref.name, args map t.exp, (targets map t.exp).asInstanceOf[Seq[LocalVar]], Label(labelName, Seq())(t.liftPos(lbl)))(t.liftPos(this))
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
    Some(Seq(s"oldCalls are only supported as statements or as the right-hand side of an assignment"))
  }

  // we do not translate this expression but `POldCall` which is created before resolution
  override def translateExp(t: Translator): ExtensionExp = throw new AssertionError(s"POldCallExp '$this' should have been transformed before typechecking")
}
