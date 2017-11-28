/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

import scala.language.implicitConversions
import org.scalatest.{Matchers, FunSuite}
import viper.silver.ast._
import viper.silver.ast.utility.Transformer._

class SimplifierTests extends FunSuite with Matchers {
  test("div and mod") {
    val e1 = Div(0, 0)()
    val e2 = Mod(0, 0)()
    val e3 = Div(8, 2)()
    val e4 = Mod(8, 3)()

    simplify(e1) should be (e1)
    simplify(e2) should be (e2)
    simplify(e3) should be (4: IntLit)
    simplify(e4) should be (2: IntLit)
  }

  implicit def int2IntLit(i: Int): IntLit = IntLit(i)()
}
