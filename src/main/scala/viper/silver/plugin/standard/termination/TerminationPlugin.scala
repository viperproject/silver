// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination

import viper.silver.ast.utility.{Functions, ViperStrategy}
import viper.silver.ast.utility.rewriter.{SimpleContext, Strategy, StrategyBuilder}
import viper.silver.ast.{Applying, Assert, CondExp, CurrentPerm, Exp, FuncApp, Function, InhaleExhaleExp, MagicWand, Method, Node, Program, Unfolding, While}
import viper.silver.parser._
import viper.silver.plugin.standard.predicateinstance.PPredicateInstance
import viper.silver.plugin.standard.termination.transformation.Trafo
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.errors.AssertFailed
import viper.silver.verifier._
import fastparse._
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.reporter.Entity

import scala.annotation.unused

class TerminationPlugin(@unused reporter: viper.silver.reporter.Reporter,
                        @unused logger: ch.qos.logback.classic.Logger,
                        config: viper.silver.frontend.SilFrontendConfig,
                        fp: FastParser) extends SilverPlugin with ParserPluginTemplate {
  import fp.{FP, keyword, exp, ParserExtension}

  private def deactivated: Boolean = config != null && config.terminationPlugin.toOption.getOrElse(false)

  /**
   * Keyword used to define decreases clauses
   */
  private val decreasesKeyword: String = "decreases"

  /**
   * Parser for decreases clauses with following possibilities.
   *
   * decreases (exp (, exp)*)? (if exp)?
   * or
   * decreases _ (if exp)?
   * or
   * decreases *
   */
  def decreases[$: P]: P[PDecreasesClause] =
    P(keyword(decreasesKeyword) ~/ (decreasesWildcard | decreasesStar | decreasesTuple) ~ ";".?)
  def decreasesTuple[$: P]: P[PDecreasesTuple] =
    FP(exp.rep(sep = ",") ~/ condition.?).map { case (pos, (a, c)) => PDecreasesTuple(a, c)(pos) }
  def decreasesWildcard[$: P]: P[PDecreasesWildcard] = FP("_" ~/ condition.?).map{ case (pos, c) => PDecreasesWildcard(c)(pos) }
  def decreasesStar[$: P]: P[PDecreasesStar] = FP("*").map{ case (pos, _) => PDecreasesStar()(pos)}
  def condition[$: P]: P[PExp] = P("if" ~/ exp)


  /**
   * Add extensions to the parser
   */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String](decreasesKeyword))
    // Add new parser to the precondition
    ParserExtension.addNewPreCondition(decreases(_))
    // Add new parser to the postcondition
    ParserExtension.addNewPostCondition(decreases(_))
    // Add new parser to the invariants
    ParserExtension.addNewInvariantCondition(decreases(_))
    input
  }

  /**
   * Transform predicate accesses in decreases clauses to predicate instances.
   */
  override def beforeResolve(input: PProgram): PProgram = {

    // Transform predicate accesses to predicate instances
    // (which are not used in the unfolding to predicate instances)
    val transformPredicateInstances = StrategyBuilder.Slim[PNode]({
      case pc@PCall(idnUse, args, None) if input.predicates.exists(_.idndef.name == idnUse.name) =>
        // PCall represents the predicate access before the translation into the AST
        PPredicateInstance(args, idnUse)(pc.pos)
      case PAccPred(pc@PCall(idnUse, args, None), _) if input.predicates.exists(_.idndef.name == idnUse.name) =>
        PPredicateInstance(args, idnUse)(pc.pos)
      case d => d
    }).recurseFunc({
      case PUnfolding(_, exp) => // ignore predicate access when it is used for unfolding
        Seq(exp)
      case PApplying(_, exp) => // ignore predicate access when it is in a magic wand
        Seq(exp)
      case PCurPerm(_) => // ignore predicate access when it is in perm
        // (However, anyways not supported in decreases clauses)
        Nil
    })

    // Apply the predicate access to instance transformation only to decreases clauses.
    val newProgram: PProgram = StrategyBuilder.Slim[PNode]({
      case dt: PDecreasesTuple => transformPredicateInstances.execute(dt): PDecreasesTuple
      case d => d
    }).recurseFunc({ // decreases clauses can only appear in functions/methods pres and methods bodies
      case PProgram(_, _, _, _, functions, _, methods, _, _) => Seq(functions, methods)
      case PFunction(_, _, _, pres, _, _) => Seq(pres)
      case PMethod(_, _, _, pres, _, body) => Seq(pres, body)
    }).execute(input)

    newProgram
  }


  /**
   * Remove decreases clauses from the AST and add them as information to the AST nodes
   */
  override def beforeVerify(input: Program): Program = {
    // Prevent potentially unsafe (mutually) recursive function calls in function postcondtions
    // for all functions that don't have a decreases clause
    lazy val cycles = Functions.findFunctionCyclesViaOptimized(input, func => func.body.toSeq)
    for (f <- input.functions) {
      val hasDecreasesClause = (f.pres ++ f.posts).exists(p => p.shallowCollect {
        case dc: DecreasesClause => dc
      }.nonEmpty)
      if (!hasDecreasesClause) {
        val funcCycles = cycles.get(f)
        val problematicFuncApps = f.posts.flatMap(p => p.shallowCollect {
          case fa: FuncApp if fa.func(input) == f => fa
          case fa: FuncApp if funcCycles.isDefined && funcCycles.get.contains(fa.func(input)) => fa
        }).toSet
        for (fa <- problematicFuncApps) {
          val calledFunc = fa.func(input)
          if (calledFunc == f) {
            if (fa.args == f.formalArgs.map(_.localVar)) {
              reportError(ConsistencyError(s"Function ${f.name} has a self-reference in its postcondition and must be proven to be well-founded. Use \"result\" instead to refer to the result of the function.", fa.pos))
            } else {
              reportError(ConsistencyError(s"Function ${f.name} has a self-reference in its postcondition and must be proven to be well-founded. Add a \"decreases\" clause to prove well-foundedness.", fa.pos))
            }
          } else {
            reportError(ConsistencyError(s"Function ${f.name} has a call to mutually-recursive function ${calledFunc.name} in its postcondition and must be proven to be well-founded. Add a \"decreases\" clause to prove well-foundedness.", fa.pos))
          }
        }
      }
    }

    // extract all decreases clauses from the program
    val newProgram: Program = extractDecreasesClauses.execute(input)

    if (deactivated) {
      // if decreases checks are deactivated, only remove the decreases clauses from the program
      newProgram
    } else {
      val trafo = new Trafo(newProgram, reportError)

      val finalProgram = trafo.getTransformedProgram
      finalProgram
    }
  }

  override def mapEntityVerificationResult(entity: Entity, input: VerificationResult): VerificationResult =
    translateVerificationResult(input)

  /**
    * Call the error transformation on possibly termination related errors.
    */
  override def mapVerificationResult(@unused program: Program, input: VerificationResult): VerificationResult =
    translateVerificationResult(input)

  private def translateVerificationResult(input: VerificationResult): VerificationResult = {
    if (deactivated) return input // if decreases checks are deactivated no verification result mapping is required.

    input match {
      case Success => input
      case Failure(errors) => Failure(errors.map({
        case a@AssertFailed(Assert(_), _, _) => a.transformedError()
        case e => e
      }))
    }
  }

  override def reportError(error: AbstractError): Unit = {
    super.reportError(error)
  }

  /**
   * Extracts all the decreases clauses from the program (i.e. functions, methods and loops in methods body)
   * and appends them to the corresponding AST node as DecreasesSpecification (Info).
   */
  private lazy val extractDecreasesClauses: Strategy[Node, SimpleContext[Node]] = ViperStrategy.Slim({
    case f: Function =>
      // decrease spec might occur as part of precondition, postcondition or both:
      val (pres, preDecreasesSpecification) = extractDecreasesClausesFromExps(f.pres)
      val (posts, postDecreasesSpecification) = extractDecreasesClausesFromExps(f.posts)

      // remove decrease spec from function:
      val newFunction = f.copy(pres = pres, posts = posts)(f.pos, f.info, f.errT)

      // add it again as info nodes:
      Seq(preDecreasesSpecification, postDecreasesSpecification).foldLeft(newFunction){
        case (modifiedFunction, Some(dc)) => dc.appendToFunction(modifiedFunction)
        case (modifiedFunction, _) => modifiedFunction
      }

    case m: Method =>
      // decrease spec might occur as part of precondition, postcondition or both:
      val (pres, preDecreasesSpecification) = extractDecreasesClausesFromExps(m.pres)
      val (posts, postDecreasesSpecification) = extractDecreasesClausesFromExps(m.posts)

      // remove decrease spec from method:
      val newMethod = m.copy(pres = pres, posts = posts)(m.pos, m.info, m.errT)

      // add it again as info nodes:
      Seq(preDecreasesSpecification, postDecreasesSpecification).foldLeft(newMethod){
        case (modifiedMethod, Some(dc)) => dc.appendToMethod(modifiedMethod)
        case (modifiedMethod, _) => modifiedMethod
      }

    case w: While =>
      val (invs, decreasesSpecification) = extractDecreasesClausesFromExps(w.invs)

      val newWhile =
        if (invs != w.invs) {
          w.copy(invs = invs)(w.pos, w.info, w.errT)
        } else {
          w
        }

      decreasesSpecification match {
        case Some(dc) => dc.appendToWhile(newWhile)
        case None => newWhile
      }
  }).recurseFunc({
    case Program(_, _, functions, _, methods, _) => Seq(functions, methods)
    case Method(_, _, _, _, _, body) => Seq(body)
  })

  /**
   * Extracts decreases clauses from the sequence of expressions.
   * Only one of each decreases clause type are extracted.
   * If more exist, then a consistency error is issued.
   *
   * @param exps sequence of expression from which decreases clauses should be extracted.
   * @return exps without decreases clauses and a decreases specification containing decreases clauses from exps.
   */
  private def extractDecreasesClausesFromExps(exps: Seq[Exp]): (Seq[Exp], Option[DecreasesSpecification]) = {
    val (decreases, pres) = exps.partition(p => p.isInstanceOf[DecreasesClause])

    val tuples = decreases.collect { case p: DecreasesTuple => p }
    // check if decreases tuple is legal
    tuples.flatMap(_.tupleExpressions).foreach(checkDecreasesTuple.execute[Exp])
    if (tuples.size > 1) {
      reportError(ConsistencyError("Multiple decreases tuple.", tuples.head.pos))
    }
    val wildcards = decreases.collect { case p: DecreasesWildcard => p }
    if (wildcards.size > 1) {
      reportError(ConsistencyError("Multiple decreases wildcard.", wildcards.head.pos))
    }
    val stars = decreases.collect { case p: DecreasesStar => p }
    if (stars.size > 1) {
      reportError(ConsistencyError("Multiple decreases star.", stars.head.pos))
    }

    if (tuples.nonEmpty || wildcards.nonEmpty || stars.nonEmpty) {
      (pres, Some(DecreasesSpecification(tuples.headOption, wildcards.headOption, stars.headOption)))
    } else {
      (exps, None)
    }
  }

  /**
   * Detects expressions which are not allowed as termination measure,
   * i.e. which are part of the decreases tuple.
   * And reports consistency errors for them.
   * (Should only be applied to the tuple expression itself and not the decreases clause)
   */
  private lazy val checkDecreasesTuple = StrategyBuilder.SlimVisitor[Node]({
    case w: MagicWand =>
      reportError(ConsistencyError("Magic wand expressions are not allowed as termination measure.", w.pos))
    case e: InhaleExhaleExp =>
      reportError(ConsistencyError("Inhale Exhale expressions are not allowed as termination measure.", e.pos))
    case _ =>
  }).recurseFunc({
    case CondExp(_, e1, e2) => Seq(e1, e2)
    case Applying(_, exp) => Seq(exp)
    case Unfolding(_, exp) => Seq(exp)
    case CurrentPerm(_) => Nil
  })
}