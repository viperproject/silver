// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silver.frontend._
import viper.silver.ast.utility.DiskLoader
import viper.silver.parser.{PProgram, ReformatPrettyPrinter}
import viper.silver.reporter.StdIOReporter

import java.nio.file.{Path, Paths}

class ReformatterTests extends AnyFunSuite {
  object Provider extends ReformatterAstProvider(StdIOReporter()) {
    def parse(content: String): PProgram = {
      doParsing(content) match {
        case Succ(r) => r
      }
    }

    def setInput(path: Path): Unit = {
      _inputFile = Some(path)
    }
  }

  def check_inner(name: String): Unit = {
    val input_path = Paths.get(getClass.getResource("reformatter/" + name + ".vpr").toURI)
    val expected_path = Paths.get(getClass.getResource("reformatter/" + name + "_expected.vpr").toURI)

    val inputProgram = DiskLoader.loadContent(input_path).get
    Provider.setInput(input_path)
    val ast = Provider.parse(inputProgram)

    val reformatted = ReformatPrettyPrinter.showProgram(ast);
    val expected = DiskLoader.loadContent(expected_path).get

    assert(reformatted == expected)
  }

  test(s"adts") {
    check_inner("adts")
  }

  test(s"annotations") {
    check_inner("annotations")
  }

  test(s"domains") {
    check_inner("domains")
  }

  test(s"expressions") {
    check_inner("expressions")
  }

  test(s"fields") {
    check_inner("fields")
  }

  test(s"functions") {
    check_inner("functions")
  }

  test(s"macros") {
    check_inner("macros")
  }

  test(s"methods") {
    check_inner("methods")
  }

  test(s"predicates") {
    check_inner("predicates")
  }

  test(s"trailing_comment") {
    check_inner("trailing_comment")
  }

  test(s"not_working") {
    check_inner("not_working")
  }
}