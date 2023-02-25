package viper.silver.plugin.standard.reasoning


import fastparse._
import org.jgrapht.Graph
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import viper.silver.ast._
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.utility.{Expressions, ViperStrategy}
import viper.silver.parser.FastParserCompanion.{LW, LeadingWhitespace, whitespace}
import viper.silver.parser._
import viper.silver.plugin.standard.reasoning.analysis.{VarAnalysisGraph, VarAnalysisSet}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier._

import scala.annotation.unused
import scala.collection.mutable

class ReasoningPlugin(@unused reporter: viper.silver.reporter.Reporter,
                      @unused logger: ch.qos.logback.classic.Logger,
                      @unused config: viper.silver.frontend.SilFrontendConfig,
                      fp: FastParser) extends SilverPlugin with ParserPluginTemplate with VarAnalysisSet with BeforeVerifyHelper {

  import fp.{FP, ParserExtension, block, exp, idndef, idnuse, keyword, trigger, typ, formalArgList, pre, post, LeadingWhitespace, oldLabel, parens}
  import viper.silver.parser.FastParserCompanion.LW


  override def reportErrorWithMsg(error: AbstractError): Unit = reportError(error)

  /** Parser for existential elimination statements. */
  def existential_elim[_: P]: P[PExistentialElim] = {
    FP(keyword("obtain") ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ keyword("where") ~/ trigger.rep ~/ exp).map { case (pos, (varList, t, e)) => PExistentialElim(varList.map { case (id, typ) => PLocalVarDecl(id, typ, None)(e.pos) }, t, e)(pos) }

  }

  /** Parser for universal introduction statements. */
  def universal_intro[_: P]: P[PUniversalIntro] =
    FP(keyword("prove") ~/ keyword("forall") ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ trigger.rep(sep = ",") ~/ keyword("assuming") ~/ exp ~/ keyword("implies") ~/ exp ~/ block).map { case (pos, (varList, triggers, e1, e2, b)) => PUniversalIntro(varList.map { case (id, typ) => PLocalVarDecl(id, typ, None)(e1.pos) }, triggers, e1, e2, b)(pos) }

  /** Parser for new influence by condition */
  def influenced_by[_: P]: P[PFlowAnnotation] =
    P(keyword("influenced") ~/ (influenced_by_var | influenced_by_heap))

  def influenced_by_var[_: P]: P[PFlowAnnotation] = {
    FP(idnuse ~/ keyword("by") ~ "{" ~/ (heap_then_vars | vars_then_opt_heap) ~/ "}").map {
      case (pos, (v_idnuse: PExp, (varList: Seq[PExp], None))) =>
        PFlowAnnotation(PVar(v_idnuse)(v_idnuse.pos), varList.map(vl => PVar(vl)(vl.pos)))(pos)
      case (pos, (v_idnuse: PExp, varList: Option[Seq[PExp]])) =>
        PFlowAnnotation(PVar(v_idnuse)(v_idnuse.pos), (varList.getOrElse(Seq()).map(vl => PVar(vl)(vl.pos))) ++ Seq(PHeap()(v_idnuse.pos)))(pos)
      case (pos, (v_idnuse: PExp, (varList1: Seq[PExp], varList2: Some[Seq[PExp]]))) =>
        PFlowAnnotation(PVar(v_idnuse)(v_idnuse.pos), ((varList1 ++ varList2.getOrElse(Seq())).map(vl => PVar(vl)(vl.pos))) ++ Seq(PHeap()(v_idnuse.pos)))(pos)
    }
  }

  def vars_then_opt_heap[_: P]: P[(Seq[PExp], Option[Seq[PExp]])] = {
    P(idnuse.rep(sep = ",") ~/ ("," ~/ keyword("heap") ~/ ("," ~/ idnuse.rep(sep = ",")).?).?.map {
      /** If there is no heap keyword */
      case None => None

      /** If there is the heap keyword but no further variables */
      case Some(None) => Some(Seq())

      /** If there is the heap keyword and additionally further variables */
      case Some(Some(varList)) => Some(varList)

    })
  }

  def heap_then_vars[_: P]: P[Option[Seq[PExp]]] = {
    P(keyword("heap") ~/ ("," ~/ idnuse.rep(sep = ",")).?)
  }


  def influenced_by_heap[_: P]: P[PFlowAnnotation] = {
    FP(keyword("heap") ~/ keyword("by") ~ "{" ~/ (heap_then_vars | vars_then_opt_heap) ~/ "}").map {
      case (pos, (varList: Seq[PExp], None)) =>
        reportError(ConsistencyError("The heap should always be influenced by the heap.", SourcePosition(pos._1.file, pos._1, pos._2)))
        PFlowAnnotation(PHeap()(pos),varList.map(vl => PVar(vl)(vl.pos)))(pos)
      case (pos, varList: Option[Seq[PExp]]) =>
        PFlowAnnotation(PHeap()(pos), (varList.getOrElse(Seq()).map(vl => PVar(vl)(vl.pos))) ++ Seq(PHeap()(pos)))(pos)
      case (pos, (varList1: Seq[PExp], varList2: Some[Seq[PExp]])) =>
        PFlowAnnotation(PHeap()(pos), (varList1 ++ varList2.getOrElse(Seq())).map(vl => PVar(vl)(vl.pos)) ++ Seq(PHeap()(pos)))(pos)
    }
  }

  def lemma[_:P]: P[PLemma] = {
    FP(keyword("isLemma")).map { case (pos,()) => PLemma()(pos)}
  }

  def oldCall[_:P]: P[POldCall] = {
    FP((idnuse.rep(sep = ",") ~ ":=").? ~ keyword("oldCall") ~ "[" ~ oldLabel ~ "]" ~ "(" ~ idnuse ~ parens(exp.rep(sep = ",")) ~ ")").map {
      case (pos, (None, lbl, method, args)) =>
        POldCall(Nil, lbl, method, args)(pos)
      case (pos, (Some(targets), lbl, method, args)) =>
        POldCall(targets, lbl, method, args)(pos)
    }
  }


  /** Add existential elimination and universal introduction to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String]("obtain", "where", "prove", "forall", "assuming", "implies"))
    ParserExtension.addNewKeywords(Set[String]("influenced", "by", "heap"))
    ParserExtension.addNewKeywords(Set[String]("isLemma"))
    ParserExtension.addNewKeywords(Set[String]("oldCall"))
    ParserExtension.addNewStmtAtEnd(existential_elim(_))
    ParserExtension.addNewStmtAtEnd(universal_intro(_))
    // Add new parser to the postcondition
    ParserExtension.addNewPostCondition(influenced_by(_))

    ParserExtension.addNewPreCondition(lemma(_))
    ParserExtension.addNewPostCondition(lemma(_))

    ParserExtension.addNewStmtAtEnd(oldCall(_))

    input
  }


  override def beforeVerify(input: Program): Program = {
    val usedNames: mutable.Set[String] = collection.mutable.Set(input.transitiveScopedDecls.map(_.name): _*)

    /** check that lemma terminates (has a decreases clause) and that it is pure */
    checkLemma(input, reportError)

    /** check that influenced by expressions are exact or overapproximate the body of the method. */
    checkInfluencedBy(input, reportError)


    ViperStrategy.Slim({
      case o@OldCall(mc,lbl) =>
        /** check whether called method is a lemma */
        val currmethod = input.findMethod(mc.methodName)
        var isLemma:Boolean = currmethod.pres.exists(p => p.isInstanceOf[Lemma])
        isLemma = isLemma || currmethod.posts.exists(p => p.isInstanceOf[Lemma])

        if (!isLemma) {
          reportError(ConsistencyError(s"method ${currmethod.name} called in old context must be lemma", o.pos))
        }


        Seqn(
          currmethod.pres.map(p =>
            Assert(LabelledOld(p, lbl.name)(p.pos))(o.pos)
          ) ++
            currmethod.posts.map(p =>
            Assume(LabelledOld(p, lbl.name)(p.pos))(o.pos)
          ),
          Seq()
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

      /** remove the influenced by postconditions.
        * remove isLemma*/
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

      case u@UniversalIntro(v, trigs, exp1, exp2, blk) =>
        val boolvar = LocalVarDecl(uniqueName("b", usedNames), Bool)(exp1.pos)

        val vars_outside_blk: mutable.Set[Declaration] = mutable.Set()

        /** Get all variables that are in scope in the current method but not inside the block */
        input.methods.foreach(m => m.body.get.ss.foreach(s => {
          if (s.contains(u)) {
            vars_outside_blk ++= mutable.Set(m.transitiveScopedDecls: _*)
          }
        }))

        /** Variables declared in the universal introduction statement are tainted */
        val tainted: Set[LocalVarDecl] = v.toSet


        /**
          * GRAPH VERSION
          */

        val graph_analysis: VarAnalysisGraph = VarAnalysisGraph(input, reportError)


        /** create graph with vars that are in scope */
        vars_outside_blk --= mutable.Set(u.transitiveScopedDecls: _*)
        vars_outside_blk ++= v
        val graph: Graph[LocalVarDecl, DefaultEdge] = new DefaultDirectedGraph[LocalVarDecl, DefaultEdge](classOf[DefaultEdge])

        var allVertices: Map[LocalVarDecl, LocalVarDecl] = Map[LocalVarDecl, LocalVarDecl]()

        /** add heap variables to vertices */
        allVertices += (graph_analysis.heap_vertex -> graph_analysis.createInitialVertex(graph_analysis.heap_vertex))

        vars_outside_blk.foreach(v => {
          if (v.isInstanceOf[LocalVarDecl]) {
            val v_decl = v.asInstanceOf[LocalVarDecl]
            val v_init = graph_analysis.createInitialVertex(v_decl)
            allVertices += (v_decl -> v_init)

            graph.addVertex(v_init)
            graph.addVertex(v_decl)
          }
        })


        /**
          * get all variables that are assigned to inside the block and take intersection with universal introduction
          * variables. If they are contained throw error since these variables should be immutable
          */
        val written_vars: Option[Set[LocalVarDecl]] = graph_analysis.writtenTo(allVertices ,blk)
        checkReassigned(written_vars, v, reportError, u)

        graph_analysis.executeTaintedGraphAnalysis(graph, tainted, blk, allVertices, u)


        /**
          * SET VERSION
          */
          /*
        val tainted_decls: Set[Declaration] = tainted.map(t => t.asInstanceOf[Declaration])
        executeTaintedSetAnalysis(tainted_decls, vars_outside_blk, blk, u, reportError)
           */

        val (new_v_map, new_exp1) = substituteWithFreshVars(v, exp1, usedNames)
        val new_exp2 = applySubstitution(new_v_map, exp2)
        val arb_vars = new_v_map.map(vars => vars._2)
        val new_trigs = trigs.map(t => Trigger(t.exps.map(e1 => applySubstitution(new_v_map, e1)))(t.pos))
        // label should also be in used Names => can also use uniqueName function
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

    }, Traverse.TopDown).execute(input)
  }
}