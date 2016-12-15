/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import java.nio.file.{Path, Paths}

import org.scalatest.{FunSuite, Matchers}
import viper.silver.ast._
import viper.silver.ast.utility._
import viper.silver.frontend.{SilFrontend, TranslatorState}
import viper.silver.verifier.AbstractError

import scala.language.implicitConversions


class RewriterTests extends FunSuite with Matchers {

  test("ImplicationToDisjunctionTests") {
    val filePrefix = "transformations\\ImplicationsToDisjunction\\"
    val files = Seq("simple", "nested", "traverseEverything")

    // Create new strategy. Parameter is the partial function that is applied on all nodes
    val strat = new Strategy[Node]({
      case Implies(left, right) => Or(Not(left)(), right)()
    }) defineDuplicator Transformer.viperDuplicator customChildren Transformer.viperChildrenSelector

    val frontend = new DummyFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend) }
  }

  test("DisjunctionToInhaleExhaleTests") {
    val filePrefix = "transformations\\DisjunctionToInhaleExhale\\"
    val files = Seq("simple", "nested", "functions")

    val strat = new StrategyC[Node, Seq[LocalVarDecl]]({
      case (Or(l, r), c) =>
        //val nonDet = NonDet(c, Bool) Cannot use this (silver angelic)
        c.custom match {
          case Seq() => InhaleExhaleExp(CondExp(TrueLit()(), l, r)(), Or(l, r)())()
          // Had to do variable renaming because otherwise variable would be quantified inside again with forall
          case varDecls => InhaleExhaleExp(CondExp(Forall(varDecls.map { vari => LocalVarDecl(vari.name + "Trafo", vari.typ)(vari.pos, vari.info) }, Seq(), TrueLit()())(), l, r)(), Or(l, r)())() // Placed true lit instead of nonDet
        }
    }) updateContext {
      case (q: QuantifiedExp, c) => c ++ q.variables
    } traverse Traverse.TopDown recurseFunc {
      case i: InhaleExhaleExp => Seq(true, false)
    } defaultContext Seq() defineDuplicator Transformer.viperDuplicator customChildren Transformer.viperChildrenSelector

    val frontend = new DummyFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend) }
  }

  test("WhileToIfAndGoto") {
    val filePrefix = "transformations\\WhileToIfAndGoto\\"
    val files = Seq("simple", "nested")

    // Example of how to transform a while loop into if and goto
    // Keeping metadata is awful when creating multiple statements from a single one and we need to think about this case, but at least it is possible
    var count = 0
    val strat = new Strategy[Node]({
      case w: While =>
        val invars: Exp = w.invs.reduce((x: Exp, y: Exp) => And(x, y)())
        count = count + 1
        Seqn(Seq(
          Assert(invars)(w.invs.head.pos, w.invs.head.info),
          If(Not(w.cond)(w.cond.pos, w.cond.info), Goto("skiploop" + count)(w.pos, w.info), Seqn(Seq())(w.pos, w.info))(w.pos, w.info),
          Label("loop" + count)(w.pos, w.info),
          w.body,
          Assert(invars)(w.invs.head.pos, w.invs.head.info),
          If(w.cond, Goto("loop" + count)(w.pos, w.info), Seqn(Seq())(w.pos, w.info))(w.pos, w.info),
          Label("skiploop" + count)(w.pos, w.info)
        ))(w.pos, w.info)

    }) defineDuplicator Transformer.viperDuplicator customChildren Transformer.viperChildrenSelector

    val frontend = new DummyFrontend
    files foreach { fileName: String => {
      count = 0
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }

  test("ManyToOneAssert") {
    val filePrefix = "transformations\\ManyToOneAssert\\"
    val files = Seq("simple", "interrupted", "nested")

    val strat = new StrategyC[Node, Int]({
      case (a: Assert, c:Context[Node, Int]) => {

        c.previous match {
          case Some(Assert(_)) => Seqn(Seq())() // If previous node is assertion we go to noop
          case _ => { // Otherwise we take all following assertions and merge their expressions into one
            c.successors.takeWhile(x => x match { // Take all following assertions
              case Assert(_) => true
              case _ => false
            }).collect({ case i: Assert => i }) match { // Collect works as a cast to list of assertion since take while does not do this
              case Seq() => a
              case as => { // Merge in case of multiple assertions
                val foldedExpr = as collect { case assertion => assertion.exp } reduceRight { (l, r) => And(l, r)() }
                Assert(And(a.exp, foldedExpr)())(a.pos, a.info)
              }
            }
          }
        }
      }
    }) defineDuplicator Transformer.viperDuplicator customChildren Transformer.viperChildrenSelector defaultContext 0

    val frontend = new DummyFrontend
    files foreach { fileName: String => {
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }

  test("CountAdditions") {
    val filePrefix = "transformations\\CountAdditions\\"
    val filesAndResults = Seq(("simple", 3), ("nested", 10), ("traverseEverything", 12))

    val query = new Query[Node, Int]({
      case a: Add => 1
    }) neutralElement 0 accumulate { (s:Seq[Int]) => s.sum }  customChildren Transformer.viperChildrenSelector

    val frontend = new DummyFrontend

    filesAndResults foreach( (tuple) => {
      val fileName = tuple._1
      val result = tuple._2

      val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
      assert(fileRes != null, s"File $filePrefix$fileName not found")
      val file = Paths.get(fileRes.toURI)

      var targetNode: Node = null
      frontend.translate(file) match {
        case (Some(p), _) => {
          targetNode = p
        }
        case (None, errors) => println("Problem with program: " + errors)
      }
      val res = query.execute(targetNode)

      println("Actual: " + res)
      println("Expected: " + result)
      assert(res == result, "Results are not equal")
    })
  }

  def executeTest(filePrefix: String, fileName: String, strat: StrategyInterface[Node], frontend: DummyFrontend): Unit = {

    val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
    val fileRef = getClass.getResource(filePrefix + fileName + "Ref.sil")
    assert(fileRes != null, s"File $filePrefix$fileName not found")
    assert(fileRef != null, s"File $filePrefix$fileName Ref not found")
    val file = Paths.get(fileRes.toURI)
    val ref = Paths.get(fileRef.toURI)


    var targetNode: Node = null
    var targetRef: Node = null

    frontend.translate(file) match {
      case (Some(p), _) => {
        targetNode = p
      }
      case (None, errors) => println("Problem with program: " + errors)
    }

    frontend.translate(ref) match {
      case (Some(p), _) => {
        targetRef = p
      }
      case (None, errors) => println("Problem with program: " + errors)
    }

    val res = strat.execute(targetNode)
    println("Old: " + targetNode.toString())
    println("New: " + res.toString())
    println("Reference: " + targetRef.toString())
    assert(res.toString() == targetRef.toString(), "Files are not equal")
  }


  class DummyFrontend extends SilFrontend {
    def createVerifier(fullCmd: _root_.scala.Predef.String) = ???

    def configureVerifier(args: Seq[String]) = ???

    def translate(silverFile: Path): (Option[Program], Seq[AbstractError]) = {
      _verifier = None
      _state = TranslatorState.Initialized

      reset(silverFile) //
      translate()

      //println(s"_program = ${_program}") /* Option[Program], set if parsing and translating worked */
      //println(s"_errors = ${_errors}")   /*  Seq[AbstractError], contains errors, if encountered */

      (_program, _errors)
    }
  }

}
