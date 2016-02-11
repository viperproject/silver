/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import org.scalatest.{FunSuite, Matchers}
import viper.silver.ast._

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
}
