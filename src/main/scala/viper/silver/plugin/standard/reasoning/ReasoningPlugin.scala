// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning

import fastparse._
import viper.silver.ast._
import viper.silver.ast.utility.rewriter.{StrategyBuilder, Traverse}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.parser.FastParserCompanion.{Pos, whitespace}
import viper.silver.parser._
import viper.silver.plugin.standard.reasoning.analysis.AnalysisUtils.{LocalVarSink, NonAssumeInfluenceSink}
import viper.silver.plugin.standard.reasoning.analysis.VarAnalysisGraphMap
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier._
import viper.silver.verifier.errors.AssertFailed

import scala.annotation.unused
import scala.collection.mutable

class ReasoningPlugin(@unused reporter: viper.silver.reporter.Reporter,
                      logger: ch.qos.logback.classic.Logger,
                      @unused config: viper.silver.frontend.SilFrontendConfig,
                      fp: FastParser) extends SilverPlugin with ParserPluginTemplate with BeforeVerifyHelper {

  import fp.{exp, ParserExtension, lineCol, _file}
  import FastParserCompanion.{ExtendedParsing, PositionParsing, reservedKw, reservedSym}

  /** Parser for existential elimination statements. */
  def existentialElim[$: P]: P[PExistentialElim] =
    P((P(PObtainKeyword) ~/ fp.nonEmptyIdnTypeList(PLocalVarDecl(_)) ~/ P(PWhereKeyword) ~/ fp.trigger.rep ~ exp).map {
      case (obtainKw, varDecls, whereKw, triggers, e) => PExistentialElim(obtainKw, varDecls, whereKw, triggers, e)(_)
    }).pos

  /** Parser for universal introduction statements. */
  def universalIntro[$: P]: P[PUniversalIntro] =
    P((P(PProveKeyword) ~/ PKw.Forall ~/ fp.nonEmptyIdnTypeList(PLocalVarDecl(_)) ~/ fp.trigger.rep ~/ P(PAssumingKeyword) ~/ exp ~/ P(PImpliesKeyword) ~/ exp ~/ fp.stmtBlock()).map {
      case (proveKw, forallKw, varDecls, triggers, assumingKw, p, impliesKw, q, b) => PUniversalIntro(proveKw, forallKw, varDecls, triggers, assumingKw, p, impliesKw, q, b)(_)
    }).pos

  /** Parser for new influence by condition */
  def flowSpec[$: P]: P[PSpecification[PInfluencedKeyword.type]] =
    P((P(PInfluencedKeyword) ~ influencedBy) map (PSpecification.apply _).tupled).pos

  def heap[$: P]: P[PHeap] = P(P(PHeapKeyword) map (PHeap(_) _)).pos // note that the parentheses are not redundant

  def assumes[$: P]: P[PAssumes] = P(P(PAssumesKeyword) map (PAssumes(_) _)).pos // note that the parentheses are not redundant

  def assumesNothingSpec[$: P]: P[PSpecification[PNothingKeyword.type]] =
    P((P(PNothingKeyword) ~ assumesNothingClause) map { case (kw, clauseFn) => pos: Pos => PSpecification(kw, clauseFn(pos))(pos) }).pos

  // assumes nothing clause is completely artificial and is created out of nowhere. Instead of taking the parser's current position,
  // we parameterize this parser by `Pos` such that the caller can pass in the position of, e.g., the corresponding keyword.
  def assumesNothingClause[$: P]: P[Pos => PAssumesNothing] = Pass(()) map { _ => PAssumesNothing()(_) }
  def singleVar[$: P]: P[PVar] = P(fp.idnuse map (PVar(_) _)).pos // note that the parentheses are not redundant
  def varsAndHeap[$: P]: P[Seq[PFlowVarOrHeap]] = (heap | singleVar).delimited(PSym.Comma).map(_.toSeq)

  def influencedBy[$: P]: P[PInfluencedBy] = P(((heap | assumes |  singleVar) ~ P(PByKeyword) ~/ varsAndHeap.braces) map {
    case (v, byKw, groupedVarList) => PInfluencedBy(v, byKw, groupedVarList)(_)
  }).pos

  /** parser for lemma annotation */
  def lemma[$: P]: P[PSpecification[PIsLemmaKeyword.type]] =
    P((P(PIsLemmaKeyword) ~ lemmaClause) map { case (kw, clauseFn) => pos: Pos => PSpecification(kw, clauseFn(pos))(pos) }).pos

  // lemma clause is completely artificial and is created out of nowhere. Instead of taking the parser's current position,
  // we parameterize this parser by `Pos` such that the caller can pass in the position of, e.g., the corresponding keyword.
  def lemmaClause[$: P]: P[Pos => PLemmaClause] = Pass(()) map { _ => PLemmaClause()(_) }

  /** parsers for oldCall statement */
  /*
  Note that the following definition of old call, i.e., `a, b := oldCall[L](lemma())` causes issues with backtracking
  because depending on whether `oldCall` is added at the beginning and end of the list of statement parsers, the parser
  has to backtrack to parse assignments and old calls, resp.
  def oldCall[$: P]: P[POldCall] =
   P(((fp.idnuse.delimited(PSym.Comma) ~ P(PSymOp.Assign)).? ~ P(POldCallKeyword) ~ fp.oldLabel.brackets ~ fp.funcApp.parens) map {
      case (lhs, oldCallKw, lbl, call) => POldCall(lhs, oldCallKw, lbl, call)(_)
   }).pos
  */
  def oldCallStmt[$: P]: P[POldCallStmt] =
      P((P(POldCallKeyword) ~/ fp.oldLabel.brackets ~/ fp.funcApp.parens) map {
      case (oldCallKw, lbl, funcApp) => POldCallStmt(oldCallKw, lbl, funcApp)(_)
    }).pos

  def oldCallExp[$: P]: P[POldCallExp] =
    P((P(POldCallKeyword) ~ fp.oldLabel.brackets ~ fp.funcApp.parens) map {
      case (oldCallKw, lbl, call) => POldCallExp(oldCallKw, lbl, call)(_)
  }).pos

  /** Add existential elimination and universal introduction to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    /** keywords for existential elimination and universal introduction */
    ParserExtension.addNewKeywords(Set(PObtainKeyword, PWhereKeyword, PProveKeyword, PAssumingKeyword, PImpliesKeyword))

    /** keywords for flow annotation and therefore modular flow analysis */
    ParserExtension.addNewKeywords(Set(PInfluencedKeyword, PByKeyword, PHeapKeyword, PNothingKeyword, PAssumesKeyword))

    /** keyword to declare a lemma and to call the lemma in an old context*/
    ParserExtension.addNewKeywords(Set(PIsLemmaKeyword))
    ParserExtension.addNewKeywords(Set(POldCallKeyword))

    /** adding existential elimination and universal introduction to the parser */
    ParserExtension.addNewStmtAtEnd(existentialElim(_))
    ParserExtension.addNewStmtAtEnd(universalIntro(_))

    /** add influenced by flow annotation to as a postcondition */
    ParserExtension.addNewPostCondition(flowSpec(_))
    ParserExtension.addNewPostCondition(assumesNothingSpec(_))

    /** add lemma as an annotation either as a pre- or a postcondition */
    ParserExtension.addNewPreCondition(lemma(_))
    ParserExtension.addNewPostCondition(lemma(_))

    /** add the oldCall as a new stmt */
    ParserExtension.addNewStmtAtEnd(oldCallStmt(_))
    ParserExtension.addNewExpAtEnd(oldCallExp(_))

    input
  }


  override def beforeResolve(input: PProgram): PProgram = {
    // we change `oldCallExp` and `oldCallStmt` (which made parsing easier) to `oldCall`, which makes the translation easier
    def transformStrategy[T <: PNode](input: T): T = StrategyBuilder.Slim[PNode]({
      case a@PAssign(delimitedTargets, op, c: POldCallExp) => POldCall(delimitedTargets, op, c.oldCallKw, c.lbl, c.call)(a.pos)
      case o@POldCallStmt(oldCallKw, lbl, call) => POldCall(PDelimited(None, Nil, None)(oldCallKw.pos), None, oldCallKw, lbl, call)(o.pos)
    }).recurseFunc({
      // only visit statements
      case _: PExp => Seq()
      case n: PNode => n.children collect { case ar: AnyRef => ar }
    }).execute(input)

    transformStrategy(input)
  }


  private def removeReasoningAnnotations(m: Method): Method = {
    val flowAnnotationAndLemmaFilter: Exp => Boolean = {
      case _: InfluencedBy | _: Lemma | _: AssumesNothing => false
      case _ => true
    }
    val postconds = m.posts.filter(flowAnnotationAndLemmaFilter)
    val preconds = m.pres.filter(flowAnnotationAndLemmaFilter)
    m.copy(pres = preconds, posts = postconds)(m.pos, m.info, m.errT)
  }

  private def translateOldCall(o: OldCall, method: Method, usedNames: mutable.Set[String]): Stmt = {
    val new_v_map: Seq[(LocalVarDecl, Exp)] = ((method.formalArgs ++ method.formalReturns) zip (o.args ++ o.rets)).map(zipped => {
      val formal_a: LocalVarDecl = zipped._1
      val arg_exp: Exp = zipped._2
      formal_a -> arg_exp
    })

    /** replace all input parameters in preconditions with the corresponding argument */
    val new_pres = method.pres.flatMap {
      case Lemma() => Seq.empty
      case p => Seq(applySubstitutionWithExp(new_v_map, p))
    }

    /** replace all input & output parameters in postconditions with the corresponding argument / result */
    val new_posts = method.posts.flatMap {
      case Lemma() => Seq.empty
      case p => Seq(applySubstitutionWithExp(new_v_map, p))
    }

    /** create new variable declarations to havoc the lhs of the oldCall */
    val rToV = o.rets.map(r => {
      val new_v = LocalVarDecl(uniqueName(".v", usedNames), r.typ)(r.pos)
      r -> new_v
    }).toMap

    val errTransformer = ErrTrafo({
      case AssertFailed(_, r, c) => PreconditionInLemmaCallFalse(o, r, c)
      case d => d
    })

    Seqn(
      // assert precondition(s)
      new_pres.map(p =>
        Assert(LabelledOld(p, o.oldLabel)(p.pos))(o.pos, errT = errTransformer)
      ) ++
        // havoc return args by assigning an unconstrained value
        o.rets.map(r => {
          LocalVarAssign(r, rToV(r).localVar)(o.pos)
        }) ++
        // inhale postcondition(s)
        new_posts.map(p =>
          Inhale(LabelledOld(p, o.oldLabel)(p.pos))(o.pos)
        ),
      rToV.values.toSeq
    )(o.pos)
  }

  private def translateExistentialElim(e: ExistentialElim, usedNames: mutable.Set[String]): Stmt = {
    val (new_v_map, new_exp) = substituteWithFreshVars(e.varList, e.exp, usedNames)
    val new_trigs = e.trigs.map(t => Trigger(t.exps.map(e1 => applySubstitution(new_v_map, e1)))(t.pos))
    val errTransformer = ErrTrafo({
      case AssertFailed(_, r, c) => ExistentialElimFailed(e, r, c)
      case d => d
    })
    Seqn(
      Seq(
        Assert(Exists(new_v_map.map(_._2), new_trigs, new_exp)(e.pos, errT = errTransformer))(e.pos)
      )
        ++
        e.varList.map(variable => LocalVarDeclStmt(variable)(variable.pos)) //list of variables
        ++
        Seq(
          Inhale(e.exp)(e.pos)
        ),
      Seq()
    )(e.pos)
  }

  private def translateUniversalIntroduction(u: UniversalIntro, usedNames: mutable.Set[String]): Stmt = {
    /** Translate the new syntax into Viper language */
    val (newVarMap, newExp1) = substituteWithFreshVars(u.varList, u.assumingExp, usedNames)
    val newExp2 = applySubstitution(newVarMap, u.implyingExp)
    val quantifiedVars = newVarMap.map(vars => vars._2)
    val newTrigs = u.triggers.map(t => Trigger(t.exps.map(e1 => applySubstitution(newVarMap, e1)))(t.pos))
    val lbl = uniqueName("l", usedNames)
    val errTransformer = ErrTrafo({
      case AssertFailed(_, r, c) => UniversalIntroFailed(u, r, c)
      case d => d
    })

    val boolvar = LocalVarDecl(uniqueName("b", usedNames), Bool)(u.assumingExp.pos)
    Seqn(
      Seq(
        Label(lbl, Seq.empty)(u.pos),
        // conditionally inhale assume expression
        If(boolvar.localVar,
          Seqn(
            Seq(Inhale(u.assumingExp)(u.assumingExp.pos)),
            Seq.empty)(u.assumingExp.pos),
          Seqn(Seq.empty, Seq.empty)(u.assumingExp.pos)
        )(u.assumingExp.pos),
        // execute block
        u.block,
        // conditionally assert imply expression
        Assert(Implies(boolvar.localVar, u.implyingExp)(u.implyingExp.pos))(u.implyingExp.pos, errT = errTransformer),
        Inhale(Forall(quantifiedVars, newTrigs, Implies(LabelledOld(newExp1, lbl)(u.implyingExp.pos), newExp2)(u.implyingExp.pos))(u.implyingExp.pos))(u.implyingExp.pos)
      ),
      Seq(boolvar) ++ u.varList
    )(u.assumingExp.pos)
  }

  override def beforeVerify(input: Program): Program = {
    val usedNames: mutable.Set[String] = collection.mutable.Set(input.transitiveScopedDecls.map(_.name): _*)

    /** check that lemma terminates (has a decreases clause) and that it is pure */
    checkLemmas(input, reportError)
    /** create graph with vars that are in scope only outside of the universal introduction code block including the quantified variables */
    val analysis: VarAnalysisGraphMap = VarAnalysisGraphMap(input, logger, reportError)

    /** Run taint analysis for all methods annotated with influences */
    analysis.checkUserProvidedInfluencesSpec()

    ViperStrategy.Slim({
      /** remove the influenced by postconditions.
        * remove isLemma */
      case m: Method => removeReasoningAnnotations(m)
      case o: OldCall =>
        /** check whether called method is a lemma */
        val currmethod = input.findMethod(o.methodName)
        if (!specifiesLemma(currmethod)) {
          reportError(ConsistencyError(s"method ${currmethod.name} called in old context must be lemma", o.pos))
        }
        translateOldCall(o, currmethod, usedNames)
      case e: ExistentialElim => translateExistentialElim(e, usedNames)
      case u@UniversalIntro(v, _, exp1, exp2, blk) =>
        /**
          * get all variables that are assigned to inside the block and take intersection with universal introduction
          * variables. If they are contained throw error since quantified variables should be immutable
          */
        val writtenVars: Set[LocalVarDecl] = analysis.getModifiedVars(blk).collect({ case v: LocalVarDecl => v})
        checkReassigned(writtenVars, v, reportError, u)
        checkInfluencedBy(input, reportError)

        /** Get all variables that are in scope in the current method */
        val tainted: Set[LocalVarDecl] = v.toSet
        val varsOutside = (input.methods
          .filter(m => m.body.isDefined)
          .flatMap(m => m.body.get.ss.filter(s => s.contains(u)).flatMap(_ => Set(m.transitiveScopedDecls: _*))).toSet -- Set(u.transitiveScopedDecls: _*)) ++ tainted

        /** Contains all variables that must not be tainted */
        val volatileVars: Set[NonAssumeInfluenceSink] = analysis.getSinksFromExpr(exp1) ++ analysis.getSinksFromExpr(exp2) -- v.map(decl => LocalVarSink(decl.localVar)).toSet
        /** execute modular flow analysis using graph maps for the universal introduction statement */
        analysis.executeTaintedGraphAnalysis(varsOutside.collect({ case v:LocalVarDecl => v }), tainted, blk, volatileVars, u)
        translateUniversalIntroduction(u, usedNames);
    }, Traverse.TopDown).execute[Program](input)
  }
}
