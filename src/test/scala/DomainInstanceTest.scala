/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import java.nio.file.{Paths, Path}

import org.scalatest.{FunSuite, Matchers}
import viper.silver.ast._
import viper.silver.frontend.{TranslatorState, SilFrontend}
import viper.silver.verifier
import viper.silver.verifier.AbstractError

import scala.language.implicitConversions



class DomainInstanceTest extends FunSuite with Matchers {
  test("Basic domain instances") {
    val t = TypeVar("T")
    val d = Domain("D",Seq(),Seq(),Seq(t))(NoPosition,NoInfo)
    val r = LocalVarDecl("r",Int)(NoPosition,NoInfo)
    val x = LocalVarDecl("x",DomainType(d,Map(t -> Int)))(NoPosition,NoInfo)
    val m = Method("m",Seq(x),Seq(r),Seq(),Seq(),Seq(),new Assert(new TrueLit()(NoPosition,NoInfo))(NoPosition,NoInfo))(NoPosition,NoInfo)
    val p = Program(Seq(d),Seq(),Seq(),Seq(),Seq(m))(NoPosition,NoInfo)

    p.groundTypeInstances.size should be (3)
  }

  test("Basic domain instances 2") {
    val frontend = new DummyFrontend
    println(System.getProperty("user.dir"))
    val fileR = getClass.getResource("all/basic/domains2.sil")
    val fileU = fileR.toURI
    val file = Paths.get(fileU)

    frontend.translate(file) match {
      case (Some(p), _) =>
        {
            p.groundTypeInstances.size should be (10)
        }
      case _ => {}
    }
  }
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
