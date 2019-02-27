// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.{FunSuite, Matchers}
import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter

class PrettyPrinterTest extends FunSuite with Matchers {
  test("The comment of nested Seqn-s is always printed") {
    val comment = "Comment XYZ"
    val a = Seqn(Seq(), Seq())(NoPosition, SimpleInfo(Seq(comment)))
    val b = Seqn(Seq(a), Seq())(NoPosition, NoInfo)
    val c = Seqn(Seq(b), Seq())(NoPosition, NoInfo)

    val printed = FastPrettyPrinter.pretty(c)

    assert(printed.contains(comment))
  }
}