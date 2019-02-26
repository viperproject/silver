// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import java.nio.file.Paths
import TestHelpers.MockSilFrontend
import org.scalatest.FunSuite
import viper.silver.ast.{Exp, Not}
import viper.silver.cfg.ConditionalEdge

class CfgTests extends FunSuite {
  val count = 100
  val prefix = "cfgtests/determinism/"
  val files = Seq("if", "while")

  files foreach { filename =>
    test(s"Determinism Test $prefix$filename") {
      val resource = getClass.getResource(prefix + filename + ".sil")
      assert(resource != null, s"File $prefix$filename not found")
      val file = Paths.get(resource.toURI)

      repeat(count) {
        val frontend = new MockSilFrontend
        frontend.translate(file) match {
          case (Some(program), _) =>
            for (method <- program.methods) {
              val cfg = method.toCfg()
              for (block <- cfg.blocks) {
                cfg.outEdges(block).toList match {
                  case ConditionalEdge(left, _, _, _) :: ConditionalEdge(right, _, _, _) :: Nil =>
                    val ord = ordered(left, right)
                    assert(ord, "Wrong order of conditional edges")
                  case _ :: Nil | Nil => // ok
                  case _ => fail("Problem with control flow graph structure")
                }
              }

            }
          case (None, errors) => fail("Problem with program: " + errors)
        }
      }
    }
  }

  private def repeat(n: Int)(body: => Unit): Unit = for (i <- 1 to n) body

  private def ordered(left: Exp, right: Exp): Boolean = (left, right) match {
    case (Not(l), Not(r)) => ordered(l, r)
    case (l, Not(r)) => l == r
    case (_, _) => false
  }
}
