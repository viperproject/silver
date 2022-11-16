package viper.silver.plugin.standard.reasoning


import fastparse.P
import viper.silver.ast._
import viper.silver.ast.utility.{Expressions, ViperStrategy}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser.{FastParser, PLocalVarDecl}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{AbstractError, Failure, Success, VerificationResult}
import viper.silver.verifier.errors.AssertFailed

import scala.annotation.unused
import scala.collection.mutable

class ReasoningPlugin(@unused reporter: viper.silver.reporter.Reporter,
                      @unused logger: ch.qos.logback.classic.Logger,
                      @unused config: viper.silver.frontend.SilFrontendConfig,
                      fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{FP, keyword, exp, ParserExtension, idndef, typ, trigger, block}

  /** Parser for existential elimination statements. */
  def existential_elim[_: P]: P[PExistentialElim] = {
    FP(keyword("obtain") ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ keyword("where") ~/ trigger.rep ~/ exp).map{ case (pos, (varList, t, e)) => PExistentialElim(varList.map { case (id,typ) => PLocalVarDecl(id,typ,None)(e.pos)}, t, e)(pos) }

  }

  /** Parser for universal introduction statements. */
  def universal_intro[_: P]: P[PUniversalIntro] = {
    FP(keyword("prove") ~/ keyword("forall") ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ trigger.rep(sep = ",") ~/ keyword("assuming") ~/ exp ~/ keyword("implies") ~/ exp ~/ block).map { case (pos, (varList, triggers, e1, e2, b)) => PUniversalIntro(varList.map { case (id, typ) => PLocalVarDecl(id, typ, None)(e1.pos) }, triggers,  e1, e2, b)(pos) }

  }

  /** Add existential elimination and universal introduction to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String]("obtain", "where", "prove", "forall", "assuming", "implies"))
    // Add new parser to the precondition
    ParserExtension.addNewStmtAtEnd(existential_elim(_))
    ParserExtension.addNewStmtAtEnd(universal_intro(_))
    input
  }


  override def beforeVerify(input: Program): Program = {
    val usedNames: mutable.Set[String] = collection.mutable.Set(input.transitiveScopedDecls.map(_.name): _*)

    def uniqueName(name: String): String = {
      var i = 1
      var newName = name
      while (usedNames.contains(newName)) {
        newName = name + i
        i += 1
      }
      usedNames.add(newName)
      newName
    }

    def substituteWithFreshVars[E <: Exp](vars: Seq[LocalVarDecl], exp: E): (Seq[(LocalVarDecl, LocalVarDecl)], E) = {
      val declMapping = vars.map(oldDecl =>
        oldDecl -> LocalVarDecl(uniqueName(oldDecl.name), oldDecl.typ)(oldDecl.pos, oldDecl.info, oldDecl.errT))
      val transformedExp = applySubstitution(declMapping, exp)
      (declMapping, transformedExp)
    }

    def applySubstitution[E <: Exp](mapping: Seq[(LocalVarDecl, LocalVarDecl)], exp: E): E = {
      Expressions.instantiateVariables(exp, mapping.map(_._1.localVar), mapping.map(_._2.localVar))
    }

    ViperStrategy.Slim({
      case e@ExistentialElim(v, trigs, exp) => { // e = ExistentialElim(vardecl, exp)
          val (new_v_map,new_exp) = substituteWithFreshVars(v, exp)
          val new_trigs = trigs.map{ case t => Trigger(t.exps.map{ case e1 => applySubstitution(new_v_map,e1)})(t.pos)}
          Seqn(
            Seq(
              Assert(Exists(new_v_map.map(_._2), new_trigs, new_exp)(e.pos, ReasoningInfo))(e.pos)
            )
            ++
            v.map { case variable => LocalVarDeclStmt(variable)(variable.pos) } //list of variables
            ++
            Seq(
              Inhale(exp)(e.pos)
            ),
            Seq()
        )(e.pos)
      }

      case u@UniversalIntro(v, trigs, exp1, exp2, blk) => {
        val boolvar = LocalVarDecl(uniqueName("b"), Bool)(exp1.pos)

        val (new_v_map,new_exp1) = substituteWithFreshVars(v, exp1)
        val new_exp2 = applySubstitution(new_v_map, exp2)
        val arb_vars = new_v_map.map{case vars => vars._2}
        val new_trigs = trigs.map{ case t => Trigger(t.exps.map{ case e1 => applySubstitution(new_v_map,e1)})(t.pos)}
        // label should also be in used Names => can also use uniqueName function
        val lbl = uniqueName("l")
        Seqn(
          Seq(
            LocalVarDeclStmt(boolvar)(u.pos)
          )
          ++
          v.map{ case vars => LocalVarDeclStmt(vars)(u.pos)}
          ++
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
            Assert(Implies(boolvar.localVar,exp2)(exp2.pos))(exp2.pos),
            Inhale(Forall(arb_vars,new_trigs, Implies(LabelledOld(new_exp1,lbl)(exp2.pos), new_exp2)(exp2.pos))(exp2.pos))(exp2.pos)
          ),
          Seq()
        )(exp1.pos)
      }

    }, Traverse.TopDown).execute(input)
  }


  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    val errors: Seq[AbstractError] = (input match {
      case Success => Seq()
      case Failure(errors) => {
        errors.map {
          case AssertFailed(a, err_reason, c) if a.info == ReasoningInfo => {
            ExistentialElimFailed(a, err_reason, c)
          }
        }
      }
    })
    if (errors.length == 0) Success
    else Failure(errors)
  }
}