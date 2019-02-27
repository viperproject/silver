// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import org.scalatest.{BeforeAndAfter, FunSuite, Matchers}
import viper.silver.testing._
import java.nio.file.{FileSystems, Path}
import scala.collection.immutable.Nil

object TestFixtures {
  val dummyFile = FileSystems.getDefault.getPath("foo.scala")
  val otherFile = FileSystems.getDefault.getPath("bar.scala")

  val actualFoo1 = DummyOutput(dummyFile, 1, "foo")
  val actualFoo2 = DummyOutput(dummyFile, 2, "foo")

  val expectedFoo1 = ExpectedOutput(OutputAnnotationId("foo", None), dummyFile, 1, 1)
  val unexpectedFoo1Carbon = UnexpectedOutput(OutputAnnotationId("foo", None), dummyFile, 1, 1, "carbon", 123)
  val missingFoo1Silicon = MissingOutput(OutputAnnotationId("foo", None), otherFile, 1, 1, "silicon", 123)
  val ignoreSiliconDummyFile = IgnoreFile(dummyFile, 1, "silicon", 12)

  val parseError = TestAnnotationParseError("some line", dummyFile, 1)
}

/** Dummy output that is not file-specific. */
case class DummyOutput(file: Path, lineNr: Int, fullId: String) extends AbstractOutput {
  def isSameLine(file: Path, lineNr: Int) =
    file == this.file && lineNr == this.lineNr
  override def toString = s"$lineNr:$fullId"
}

/** Tests [[viper.silver.testing.OutputMatcher]]. */
class OutputMatcherTest extends FunSuite with BeforeAndAfter with Matchers {
  import TestFixtures._

  test("expected output") {
    OutputMatcher(Seq(actualFoo1), Seq(expectedFoo1)).errors should be (Nil)

    OutputMatcher(Seq(), Seq(expectedFoo1)).errors should be
      Seq(TestExpectedButMissingOutputError(expectedFoo1))

    OutputMatcher(Seq(actualFoo2), Seq(expectedFoo1)).errors.toSet should be
      Set(TestExpectedButMissingOutputError(expectedFoo1), TestAdditionalOutputError(actualFoo2))
  }

  test("unexpected output") {
    OutputMatcher(Seq(actualFoo1), Seq(unexpectedFoo1Carbon)).errors should be (Nil)

    OutputMatcher(Seq(), Seq(unexpectedFoo1Carbon)).errors should be
      Seq(TestUnexpectedButMissingOutputError(unexpectedFoo1Carbon))

    OutputMatcher(Seq(actualFoo2), Seq(unexpectedFoo1Carbon)).errors.toSet should be
      Set(TestUnexpectedButMissingOutputError(unexpectedFoo1Carbon), TestAdditionalOutputError(actualFoo2))
  }

  test("missing output") {
    OutputMatcher(Seq(actualFoo1), Seq(missingFoo1Silicon)).errors should be
      Seq(TestMissingButPresentOutputError(missingFoo1Silicon, actualFoo1))
  }

  test("additional output") {
    OutputMatcher(Seq(actualFoo1), Seq()).errors should be
      Seq(TestAdditionalOutputError(actualFoo2))
  }
}

/** Tests [[viper.silver.testing.TestAnnotations]]. */
class TestAnnotationsTest extends FunSuite with BeforeAndAfter with Matchers {
  import TestFixtures._

  val annotations = TestAnnotations(
    errors = Seq(parseError),
    annotations = Seq(expectedFoo1, unexpectedFoo1Carbon, missingFoo1Silicon))

  test("filtering by project") {
    val newAnnotations = annotations.filterByProject(new ProjectInfo(List("Carbon")))
    newAnnotations.errors should be (annotations.errors)
    newAnnotations.annotations should be (Seq(expectedFoo1, unexpectedFoo1Carbon))
  }

  test("filtering by key id prefix") {
    val annotations = TestAnnotations(
      errors = Seq(parseError),
      annotations = Seq(expectedFoo1, ignoreSiliconDummyFile))

    var newAnnotations = annotations.filterByKeyIdPrefix("foo")
    newAnnotations.errors should be (annotations.errors)
    newAnnotations.annotations should be (Seq(expectedFoo1, ignoreSiliconDummyFile))

    newAnnotations = annotations.filterByKeyIdPrefix("something.else")
    newAnnotations.errors should be (annotations.errors)
    newAnnotations.annotations should be (Seq(ignoreSiliconDummyFile))
  }

  test("has errors") {
    annotations.hasErrors should be (true)
    TestAnnotations(errors = Nil, annotations = Nil).hasErrors should be (false)
  }

  test("is file ignored") {
    val a = TestAnnotations(Nil, Seq(ignoreSiliconDummyFile))
    a.isFileIgnored(dummyFile, "Silicon") should be (true)
    a.isFileIgnored(dummyFile, "Carbon") should be (false)
    a.isFileIgnored(otherFile, "Silicon") should be (false)
  }

  test("output annotations") {
    val a = TestAnnotations(Nil, Seq(ignoreSiliconDummyFile, expectedFoo1))
    a.outputAnnotations should be (Seq(expectedFoo1))
  }
}

/** Tests [[viper.silver.testing.OutputAnnotationId]]. */
class OutputAnnotationIdTest extends FunSuite with BeforeAndAfter with Matchers {
  val foo = OutputAnnotationId("foo", None)
  val fooBar = OutputAnnotationId("foo", Some("bar"))

  test("toString") {
    foo.toString should be ("foo")
    fooBar.toString should be ("foo:bar")
  }

  test("matches") {
    foo.matches("foo") should be (true)
    foo.matches("foo:some-detail") should be (true)
    fooBar.matches("foo") should be (false)
    fooBar.matches("foo:bar") should be (true)
    fooBar.matches("foo:baz") should be (false)
  }
}
