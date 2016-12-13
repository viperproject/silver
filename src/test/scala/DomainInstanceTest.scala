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



class DomainInstanceTest extends FunSuite with Matchers {
 /* test("Basic domain instances") {
    val t = TypeVar("T")
    val d = Domain("D", Seq(), Seq(), Seq(t))(NoPosition, NoInfo)
    val r = LocalVarDecl("r", Int)(NoPosition, NoInfo)
    val x = LocalVarDecl("x", DomainType(d, Map(t -> Int)))(NoPosition, NoInfo)
    val m = Method("m", Seq(x), Seq(r), Seq(), Seq(), Seq(), new Assert(new TrueLit()(NoPosition, NoInfo))(NoPosition, NoInfo))(NoPosition, NoInfo)
    val p = Program(Seq(d), Seq(), Seq(), Seq(), Seq(m))(NoPosition, NoInfo)

    p.groundTypeInstances.size should be(3)
  }*/

  test("Transfuckingformer") {
    val frontend = new DummyFrontend
    println(System.getProperty("user.dir"))
    val fileR = getClass.getResource("transformations\\custom\\implications.sil")
    val fileU = fileR.toURI
    val file = Paths.get(fileU)

    var targetNode:Node = null

    val strat = new StrategyC[Node, Seq[LocalVarDecl]]({
      case (Or(l, r), c) =>
        //val nonDet = NonDet(c, Bool) Cannot use this (silver angelic)
        c match {
          case None => InhaleExhaleExp(CondExp(TrueLit()(), l, r)(), Or(l, r)())()
          case Some(context) => InhaleExhaleExp(CondExp(Forall(context, Seq(), TrueLit()())(), l, r)(), Or(l, r)())() // Placed true lit instead of nonDet
        }
    }) updateContext {
      case (q:QuantifiedExp, None) => Some(q.variables)
      case (q:QuantifiedExp, Some(c)) => Some(c ++ q.variables)
    } traverse Traverse.TopDown recurseFunc {
      case i: InhaleExhaleExp => Seq(true, false)
    } defineDuplicator Transformer.viperDuplicator customChildren Transformer.viperChildrenSelector

    frontend.translate(file) match {
      case (Some(p), _) => {
        targetNode = p
      }
      case (None, errors) => println("No program: " + errors)
    }
    val res = strat.execute(targetNode)
    println("Old: " + targetNode.toString())
    println("New: " + res.toString())
  }

 /* test("Basic domain instances 2") {
    val frontend = new DummyFrontend
    println(System.getProperty("user.dir"))
    val fileR = getClass.getResource("all/basic/domains2.sil")
    val fileU = fileR.toURI
    val file = Paths.get(fileU)

    frontend.translate(file) match {
      case (Some(p), _) => {
//        DomainInstances.showInstanceMembers(p)
        p.groundTypeInstances.size should be(259)

  //      DomainInstances.showInstanceMembers(p)
        for (gi <- p.groundTypeInstances)
          gi match {
            case dt: DomainType => {
              dt.domainName should not be "D1"
            }
            case _ =>
          }

        p.groundTypeInstances.count(
          _ match { case dt: DomainType => dt.domainName == "D10" && dt.typVarsMap.values.forall(_ == Int)
          case _ => false
          }
        ) should be(1)
        p.groundTypeInstances.count(
          _ match { case dt: DomainType => dt.domainName == "D10"
          case _ => false
          }
        ) should be(256)
      }
      case _ => {}
    }
  }

  test("Domain instances recursion threshold") {
    val frontend = new DummyFrontend
    println(System.getProperty("user.dir"))
    val fileR = getClass.getResource("all/basic/domains_threshold.sil")
    val fileU = fileR.toURI
    val file = Paths.get(fileU)

    frontend.translate(file) match {
      case (Some(p), _) => {
//        DomainInstances.showInstanceMembers(p)
        p.groundTypeInstances.size should be(7)

/*        for (gi <- p.groundTypeInstances)
          gi match {
            case dt: DomainType => {
              dt.domainName should not be "D1"
            }
            case _ =>
          }
  */
/*        p.groundTypeInstances.count(
          _ match { case dt: DomainType => dt.domainName == "D10" && dt.typVarsMap.values.forall(_ == Int)
          case _ => false
          }
        ) should be(1)
        p.groundTypeInstances.count(
          _ match { case dt: DomainType => dt.domainName == "D10"
          case _ => false
          }
        ) should be(256)*/
      }
      case _ => {}
    }

  }*/
}


class DummyFrontend extends SilFrontend {
  def createVerifier(fullCmd: _root_.scala.Predef.String) = ???
  def configureVerifier(args: Seq[String]) = ???

  def translate(silverFile: Path): (Option[Program],Seq[AbstractError]) = {
    _verifier = None
    _state = TranslatorState.Initialized

    reset(silverFile)               //
    translate()

    //println(s"_program = ${_program}") /* Option[Program], set if parsing and translating worked */
    //println(s"_errors = ${_errors}")   /*  Seq[AbstractError], contains errors, if encountered */

    (_program, _errors)
  }
}
