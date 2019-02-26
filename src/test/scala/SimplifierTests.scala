// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import scala.language.implicitConversions
import org.scalatest.{Matchers, FunSuite}
import viper.silver.ast._
import viper.silver.ast.utility.Simplifier._

class SimplifierTests extends FunSuite with Matchers {
  test("div") {
    simplify(Div(0, 0)()) should be(Div(0, 0)())
    simplify(Div(8, 2)()) should be(4: IntLit)
  }

  test("mod") {
    simplify(Mod(0, 0)()) should be (Mod(0, 0)())
    simplify(Mod(8, 3)()) should be (2: IntLit)
    simplify(Mod(3, 8)()) should be (3: IntLit)
    simplify(Mod(8, -3)()) should be (2: IntLit)
    simplify(Mod(3, -8)()) should be (3: IntLit)
    simplify(Mod(-8, 3)()) should be (1: IntLit)
    simplify(Mod(-3, 8)()) should be (5: IntLit)
    simplify(Mod(-8, -3)()) should be (1: IntLit)
    simplify(Mod(-3, -8)()) should be (5: IntLit)
  }

  implicit def int2IntLit(i: Int): IntLit = IntLit(i)()
}
