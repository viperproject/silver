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

  //  test("ImplicationToDisjunctionTests") {
  //    // Create new strategy. Parameter is the partial function that is applied on all nodes
  //    val strat = new Strategy[Node]({
  //      case Implies(left, right) => Or(Not(left)(), right)()
  //    })
  //
  //    // Example of how to execute the strategy with a dummy node
  //    var targetNode: Node = Div(0, 0)()
  //    var res = strat.execute(targetNode)
  //    println(targetNode.toString())
  //    println(res.toString())
  //
  //    TrueLit()() should be (TrueLit()())
  //  }

  test("DisjunctionToInhaleExhaleTests") {
    val filePrefix = "transformations\\DisjunctionToInhaleExhale\\"
    val files = Seq(/*"simple", */"nested")

    val frontend = new DummyFrontend

    val strat = new StrategyC[Node, Seq[LocalVarDecl]]({
      case (Or(l, r), c) =>
        //val nonDet = NonDet(c, Bool) Cannot use this (silver angelic)
        c match {
          case None => InhaleExhaleExp(CondExp(TrueLit()(), l, r)(), Or(l, r)())()
          // Had to do variable renaming because otherwise variable would be quantified inside again with forall
          case Some(context) => InhaleExhaleExp(CondExp(Forall(context.map { vari => LocalVarDecl(vari.name + "Trafo", vari.typ)(vari.pos, vari.info)}, Seq(), TrueLit()())(), l, r)(), Or(l, r)())() // Placed true lit instead of nonDet
        }
    }) updateContext {
      case (q: QuantifiedExp, None) => Some(q.variables)
      case (q: QuantifiedExp, Some(c)) => Some(c ++ q.variables)
    } traverse Traverse.TopDown recurseFunc {
      case i: InhaleExhaleExp => Seq(true, false)
    } defineDuplicator Transformer.viperDuplicator customChildren Transformer.viperChildrenSelector

    files foreach { (fileName) => {
      val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
      val fileRef = getClass.getResource(filePrefix + fileName + "Ref.sil")
      assert(fileRes != null, s"File $filePrefix$fileName not found")
      assert( fileRef != null, s"File $filePrefix$fileName Ref not found")
      val file = Paths.get(fileRes.toURI)
      val ref = Paths.get(fileRef.toURI)

      var targetNode: Node = null
      var targetRef: Node = null

      frontend.translate(file) match {
        case (Some(p), _) => {
          targetNode = p
        }
        case (None, errors) => println("No program: " + errors)
      }

      frontend.translate(ref) match {
        case (Some(p), _) => {
          targetRef = p
        }
        case (None, errors) => println("No program: " + errors)
      }

      val res = strat.execute(targetNode)
      println("Old: " + targetNode.toString())
      println("New: " + res.toString())
      println("Reference: " + targetRef.toString())
      assert(res.toString() == targetRef.toString(), "Files are not equal")
    }
    }
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
