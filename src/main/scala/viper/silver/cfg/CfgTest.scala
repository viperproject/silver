// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.cfg

import java.nio.file.{Files, Path, Paths}

import fastparse.core.Parsed.Success
import viper.silver.parser.{FastParser, PProgram, Resolver, Translator}
import viper.silver.verifier.ParseWarning

import scala.io.Source

object CfgTest {
  def main(args: Array[String]): Unit = {
    if (args.isEmpty) throw new RuntimeException("No input file specified")
    val path = args(0)

    val file = Paths.get(path)
    val string = Source.fromInputStream(Files.newInputStream(file)).mkString

    val parsed = parse(string, file).get
    val resolver = Resolver(parsed)
    val resolved = resolver.run.get
    val translator = Translator(resolved)
    val program = translator.translate.get

    for (method <- program.methods) {
      val cfg = method.toCfg()
      println(method.name)
      println(cfg.toDot)
    }
  }

  private def parse(input: String, file: Path): Option[PProgram] = {
    val result = FastParser.parse(input, file)
    result match {
      case Success(program@PProgram(_, _, _, _, _, _, _,_, errors), _) =>
        if (errors.isEmpty || errors.forall(_.isInstanceOf[ParseWarning])) Some(program)
        else None
      case _ => None
    }
  }
}