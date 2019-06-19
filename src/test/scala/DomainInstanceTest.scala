// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import java.nio.file.Paths
import TestHelpers.MockSilFrontend
import org.scalatest.{FunSuite, Matchers}
import viper.silver.ast._

class DomainInstanceTest extends FunSuite with Matchers {
  test("Basic domain instances") {
    val t = TypeVar("T")
    val d = Domain("D", Seq(), Seq(), Seq(t))(NoPosition, NoInfo)
    val r = LocalVarDecl("r", Int)(NoPosition, NoInfo)
    val x = LocalVarDecl("x", DomainType(d, Map(t -> Int)))(NoPosition, NoInfo)
    val m = Method("m", Seq(x), Seq(r), Seq(), Seq(), Some(Seqn(Seq(Assert(TrueLit()(NoPosition, NoInfo))(NoPosition, NoInfo)), Seq())(NoPosition, NoInfo)))(NoPosition, NoInfo)
    val p = Program(Seq(d), Seq(), Seq(), Seq(), Seq(m), Seq())(NoPosition, NoInfo)

    p.groundTypeInstances.size should be(3)
  }

  test("Basic domain instances 2") {
    val frontend = new MockSilFrontend
    val fileN = "all/domains/domains2.sil"
    val fileR = getClass.getResource(fileN)
    assert(fileR != null, s"File $fileN not found")
    val fileU = fileR.toURI
    val file = Paths.get(fileU)

    frontend.translate(file) match {
      case (Some(p), _) =>
        //        DomainInstances.showInstanceMembers(p)
//        p.groundTypeInstances.size should be(259) /* TODO: See Silver issue #196 */

        //      DomainInstances.showInstanceMembers(p)
        for (gi <- p.groundTypeInstances)
          gi match {
            case dt: DomainType =>
              dt.domainName should not be "D1"
            case _ =>
          }

        p.groundTypeInstances.count {
          case dt: DomainType => dt.domainName == "D10" && dt.typVarsMap.values.forall(_ == Int)
          case _ => false
        } should be(1)

        p.groundTypeInstances.count {
          case dt: DomainType => dt.domainName == "D10"
          case _ => false
        } should be(256)

      case _ =>
    }
  }

  test("Domain instances recursion threshold") {
    val frontend = new MockSilFrontend
    val fileN = "all/domains/domains_threshold.sil"
    val fileR = getClass.getResource(fileN)
    assert(fileR != null, s"File $fileN not found")
    val fileU = fileR.toURI
    val file = Paths.get(fileU)

    frontend.translate(file) match {
      case (Some(p), _) =>
//        viper.silver.ast.utility.DomainInstances.showInstanceMembers(p)
        p.groundTypeInstances.size should be(8)

        /* 2017-04-28 Malte:
         *   Deactivated all remaining assertions since they don't make any sense to me
         *   (and because they fail). In particular, the assertions expect D1 to not be
         *   instantiated and D10 to be, but D1 is the only domain in domains_threshold.sil.
         */

//        for (gi <- p.groundTypeInstances)
//          gi match {
//            case dt: DomainType => dt.domainName should not be "D1"
//            case _ =>
//          }

//        p.groundTypeInstances.count {
//          case dt: DomainType => dt.domainName == "D10" && dt.typVarsMap.values.forall(_ == Int)
//          case _ => false
//        } should be(1)

//        p.groundTypeInstances.count {
//          case dt: DomainType => dt.domainName == "D10"
//          case _ => false
//        } should be(256)

      case (None, errors) =>
        fail(s"Expected a parsed program, but got: $errors")
    }
  }
}
