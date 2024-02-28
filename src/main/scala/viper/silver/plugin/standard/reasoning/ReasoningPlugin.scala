// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning

import fastparse._
import org.jgrapht.Graph
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import viper.silver.ast._
import viper.silver.ast.utility.rewriter.{StrategyBuilder, Traverse}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser._
import viper.silver.plugin.standard.reasoning.analysis.{SetGraphComparison, VarAnalysisGraph}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier._

import scala.annotation.unused
import scala.collection.mutable

class ReasoningPlugin(@unused reporter: viper.silver.reporter.Reporter,
                      @unused logger: ch.qos.logback.classic.Logger,
                      @unused config: viper.silver.frontend.SilFrontendConfig,
                      fp: FastParser) extends SilverPlugin with ParserPluginTemplate with SetGraphComparison with BeforeVerifyHelper {

  import fp.{exp, ParserExtension, lineCol, _file}
  import FastParserCompanion.{ExtendedParsing, PositionParsing, reservedKw, reservedSym}


  override def reportErrorWithMsg(error: AbstractError): Unit = reportError(error)

  /** Parser for existential elimination statements. */
  def existential_elim[$: P]: P[PExistentialElim] =
    P((P(PObtainKeyword) ~/ fp.nonEmptyIdnTypeList(PLocalVarDecl(_)) ~/ P(PWhereKeyword) ~/ fp.trigger.rep ~ exp).map {
      case (obtainKw, varDecls, whereKw, triggers, e) => PExistentialElim(obtainKw, varDecls, whereKw, triggers, e)(_)
    }).pos

  /** Parser for universal introduction statements. */
  def universal_intro[$: P]: P[PUniversalIntro] =
    P((P(PProveKeyword) ~/ PKw.Forall ~/ fp.nonEmptyIdnTypeList(PLocalVarDecl(_)) ~/ fp.trigger.rep ~/ P(PAssumingKeyword) ~/ exp ~/ P(PImpliesKeyword) ~/ exp ~/ fp.stmtBlock()).map {
      case (proveKw, forallKw, varDecls, triggers, assumingKw, p, impliesKw, q, b) => PUniversalIntro(proveKw, forallKw, varDecls, triggers, assumingKw, p, impliesKw, q, b)(_)
    }).pos

  /** Parser for new influence by condition */
  def flowSpec[$: P]: P[PSpecification[PInfluencedKeyword.type]] =
    P((P(PInfluencedKeyword) ~ influenced_by) map (PSpecification.apply _).tupled).pos

  def heap[$: P]: P[PHeap] = P(P(PHeapKeyword) map (PHeap(_) _)).pos // note that the parentheses are not redundant

  def singleVar[$: P]: P[PVar] = P(fp.idnuse map (PVar(_) _)).pos // note that the parentheses are not redundant
  def vars_and_heap[$: P]: P[Seq[PFlowVar]] = (heap | singleVar).delimited(PSym.Comma).map(_.toSeq)

  def influenced_by[$: P]: P[PFlowAnnotation] = P(((heap | singleVar) ~ P(PByKeyword) ~/ vars_and_heap.braces) map {
    case (v, byKw, groupedVarList) => PFlowAnnotation(v, byKw, groupedVarList)(_)
  }).pos

  /** parser for lemma annotation */
  def lemma[$: P]: P[PSpecification[PIsLemmaKeyword.type]] =
    P((P(PIsLemmaKeyword) ~ lemmaClause) map (PSpecification.apply _).tupled).pos

  // lemma clause is completely artificial and is created out of nowhere at the parser's current position
  def lemmaClause[$: P]: P[PLemmaClause] = (Pass(()) map { _ => PLemmaClause()(_) }).pos

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
    ParserExtension.addNewKeywords(Set(PInfluencedKeyword, PByKeyword, PHeapKeyword))

    /** keyword to declare a lemma and to call the lemma in an old context*/
    ParserExtension.addNewKeywords(Set(PIsLemmaKeyword))
    ParserExtension.addNewKeywords(Set(POldCallKeyword))

    /** adding existential elimination and universal introduction to the parser */
    ParserExtension.addNewStmtAtEnd(existential_elim(_))
    ParserExtension.addNewStmtAtEnd(universal_intro(_))

    /** add influenced by flow annotation to as a postcondition */
    ParserExtension.addNewPostCondition(flowSpec(_))

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


  override def beforeVerify(input: Program): Program = {

    /** for evaluation purposes */
    //val begin_time = System.currentTimeMillis()

    val usedNames: mutable.Set[String] = collection.mutable.Set(input.transitiveScopedDecls.map(_.name): _*)

    /** check that lemma terminates (has a decreases clause) and that it is pure */
    checkLemma(input, reportError)

    /** check that influenced by expressions are exact or overapproximate the body of the method. */
    checkInfluencedBy(input, reportError)


    /** method call to compare the analysis of the set-approach vs. the graph approach */
    //compareGraphSet(input, reportError)


    val newAst: Program = ViperStrategy.Slim({

      /** remove the influenced by postconditions.
        * remove isLemma */
      case m: Method =>


        var postconds: Seq[Exp] = Seq()
        m.posts.foreach {
          case _: FlowAnnotation =>
            postconds = postconds
          case _: Lemma =>
            postconds = postconds
          case s@_ =>
            postconds = postconds ++ Seq(s)
        }
        var preconds: Seq[Exp] = Seq()
        m.pres.foreach {
          case _: Lemma =>
            preconds = preconds
          case s@_ =>
            preconds = preconds ++ Seq(s)
        }
        val newMethod =
          if (postconds != m.posts || preconds != m.pres) {
            m.copy(pres = preconds, posts = postconds)(m.pos, m.info, m.errT)
          } else {
            m
          }

        newMethod

      case o@OldCall(methodName, args, rets, lbl) =>
        /** check whether called method is a lemma */
        val currmethod = input.findMethod(methodName)
        val isLemma = (currmethod.pres ++ currmethod.posts).exists {
          case _: Lemma => true
          case _ => false
        }

        if (!isLemma) {
          reportError(ConsistencyError(s"method ${currmethod.name} called in old context must be lemma", o.pos))
        }

        var new_pres: Seq[Exp] = Seq()
        var new_posts: Seq[Exp] = Seq()
        var new_v_map: Seq[(LocalVarDecl, Exp)] =
          (args zip currmethod.formalArgs).map(zipped => {
          val formal_a: LocalVarDecl = zipped._2
          val arg_exp: Exp = zipped._1
          formal_a -> arg_exp
        })
        new_v_map ++=
          (rets zip currmethod.formalReturns).map(zipped => {
            val formal_r: LocalVarDecl = zipped._2
            val r: LocalVar = zipped._1
            formal_r -> r
          })
        /** replace all variables in precondition with fresh variables */
        currmethod.pres.foreach {
          case Lemma() => ()
          case p =>
            new_pres ++= Seq(applySubstitutionWithExp(new_v_map, p))
        }

        /** replace all variables in postcondition with fresh variables */
        currmethod.posts.foreach {
          case Lemma() => ()
          case p =>
            new_posts ++= Seq(applySubstitutionWithExp(new_v_map, p))
        }

        /** create new variable declarations to havoc the lhs of the oldCall */
        var new_v_decls: Seq[LocalVarDecl] = Seq()
        var rTov: Map[LocalVar,LocalVarDecl] = Map()
        for (r <- rets) {
          val new_v = LocalVarDecl(uniqueName(".v", usedNames),r.typ)(r.pos)
          new_v_decls = new_v_decls ++ Seq(new_v)
          rTov += (r -> new_v)
        }


        Seqn(
          new_pres.map(p =>
            Assert(LabelledOld(p, lbl)(p.pos))(o.pos)
          )
            ++

            rets.map(r => {
              LocalVarAssign(r,rTov(r).localVar)(o.pos)
            })
            ++


            new_posts.map(p =>
            Inhale(LabelledOld(p, lbl)(p.pos))(o.pos)
          ),
          new_v_decls
        )(o.pos)


      case e@ExistentialElim(v, trigs, exp) =>
        val (new_v_map, new_exp) = substituteWithFreshVars(v, exp, usedNames)
        val new_trigs = trigs.map(t => Trigger(t.exps.map(e1 => applySubstitution(new_v_map, e1)))(t.pos))
        Seqn(
          Seq(
            Assert(Exists(new_v_map.map(_._2), new_trigs, new_exp)(e.pos, ReasoningInfo))(e.pos)
          )
            ++
            v.map(variable => LocalVarDeclStmt(variable)(variable.pos)) //list of variables
            ++
            Seq(
              Inhale(exp)(e.pos)
            ),
          Seq()
        )(e.pos)

      case u@UniversalIntro(v, trigs, exp1, exp2, blk) =>
        val boolvar = LocalVarDecl(uniqueName("b", usedNames), Bool)(exp1.pos)

        val vars_outside_blk: mutable.Set[Declaration] = mutable.Set()

        /** Get all variables that are in scope in the current method but not inside the block */
        input.methods.foreach(m => m.body.get.ss.foreach(s => {
          if (s.contains(u)) {
            vars_outside_blk ++= mutable.Set(m.transitiveScopedDecls: _*)
          }
        }))

        /** Qunatified variables in the universal introduction statement are tainted */
        val tainted: Set[LocalVarDecl] = v.toSet


        /**
          * GRAPH VERSION
          */

        val graph_analysis: VarAnalysisGraph = VarAnalysisGraph(input, reportError)


        /** create graph with vars that are in scope only outside of the universal introduction code block including the qunatified variables*/
        vars_outside_blk --= mutable.Set(u.transitiveScopedDecls: _*)
        vars_outside_blk ++= v

        val graph: Graph[LocalVarDecl, DefaultEdge] = new DefaultDirectedGraph[LocalVarDecl, DefaultEdge](classOf[DefaultEdge])

        /** Map that contains all variables where the key is represents the variables final value and the value the variables initial value before a statement. */
        var allVertices: Map[LocalVarDecl, LocalVarDecl] = Map[LocalVarDecl, LocalVarDecl]()

        /** add heap variables to vertices */
        allVertices += (graph_analysis.heap_vertex -> graph_analysis.createInitialVertex(graph_analysis.heap_vertex))

        vars_outside_blk.foreach {
          case v_decl: LocalVarDecl =>
            val v_init = graph_analysis.createInitialVertex(v_decl)
            allVertices += (v_decl -> v_init)

            /** add all variable to the graph */
            graph.addVertex(v_init)
            graph.addVertex(v_decl)
          case _ =>
        }

        /**
          * get all variables that are assigned to inside the block and take intersection with universal introduction
          * variables. If they are contained throw error since quantified variables should be immutable
          */
        val written_vars: Option[Set[LocalVarDecl]] = graph_analysis.getModifiedVars(allVertices ,blk)
        checkReassigned(written_vars, v, reportError, u)

        /** execute modular flow analysis using graphs for the universal introduction statement */
        graph_analysis.executeTaintedGraphAnalysis(tainted, blk, allVertices, u)

        /**
          * SET VERSION
          */
        /*
        val tainted_decls: Set[Declaration] = tainted.map(t => t.asInstanceOf[Declaration])
        executeTaintedSetAnalysis(tainted_decls, vars_outside_blk, blk, u, reportError)
        */

        /** Translate the new syntax into Viper language */
        val (new_v_map, new_exp1) = substituteWithFreshVars(v, exp1, usedNames)
        val new_exp2 = applySubstitution(new_v_map, exp2)
        val arb_vars = new_v_map.map(vars => vars._2)
        val new_trigs = trigs.map(t => Trigger(t.exps.map(e1 => applySubstitution(new_v_map, e1)))(t.pos))
        val lbl = uniqueName("l", usedNames)

        Seqn(
          Seq(
            Label(lbl, Seq())(u.pos),
            If(boolvar.localVar,
              Seqn(
                Seq(
                  Inhale(exp1)(exp1.pos)
                ),
                Seq())(exp1.pos),
              Seqn(Seq(), Seq())(exp1.pos)

            )(exp1.pos),
            blk,
            Assert(Implies(boolvar.localVar, exp2)(exp2.pos))(exp2.pos),
            Inhale(Forall(arb_vars, new_trigs, Implies(LabelledOld(new_exp1, lbl)(exp2.pos), new_exp2)(exp2.pos))(exp2.pos))(exp2.pos)
          ),
          Seq(boolvar) ++ v
        )(exp1.pos)

    }, Traverse.TopDown).execute[Program](input)
    /** for evaluation purposes */
    /*
    val end_time = System.currentTimeMillis()
    println("--------------------------------------------------------------------------")
    println("beforeVerify time: " + (end_time - begin_time) + "ms")
    println("--------------------------------------------------------------------------")
    */
    newAst
  }
}
