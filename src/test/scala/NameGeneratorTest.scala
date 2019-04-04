// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import viper.silver.utility.{SilNameGenerator, NameGenerator}
import org.scalatest.{BeforeAndAfter, FunSuite}

class NameGeneratorTest extends FunSuite with BeforeAndAfter {
  var gen: SilNameGenerator = null
  var sub: NameGenerator = null
  var subsub: NameGenerator = null
  var subsub2: NameGenerator = null
  var sub2: NameGenerator = null
  var sub2sub: NameGenerator = null

  before {
    gen = new SilNameGenerator()
    sub = gen.createSubContext()
    subsub = sub.createSubContext()
    subsub2 = sub.createSubContext()
    sub2 = gen.createSubContext()
    sub2sub = sub2.createSubContext()
  }

  def assertEq(a: String, b: String) = {
    assert(a == b, s"""Expected "$b" and got "$a".""")
  }

  /* Note: When `testArgs` is populated, gen is still null - `gen` will only be initialised
   * right before each test case is called (by the `before` method above).
   */
  val testArgs = List(
    ((s: String) => gen.createIdentifier(s), "createIdentifier"),
    ((s: String) => gen.createUniqueIdentifier(s), "createUniqueIdentifier"))

  testArgs foreach { case (f, name) =>
    test("Valid Identifier Unchanged " + name) {
      assertEq(f("asdf"), "asdf")
    }

    test("Empty Identifier " + name) {
      assertEq(f(""), gen.defaultIdent)
    }

    test("Invalid First Letter " + name) {
      assertEq(f("9"), gen.defaultIdent + "9")
      assertEq(f("1a"), gen.defaultIdent + "1a")
      assertEq(f("`a"), gen.defaultIdent + "a")
    }

    test("Reserved name " + name) {
      assertEq(f("function"), gen.defaultIdent + "function")
    }

    test("Replacing " + name) {
      assertEq(f("!!=<"), "bangbangeqless")
    }

    test("Deleting " + name) {
      assertEq(f("a′"), "a")
    }
  }

  test("Unique Counter") {
    assertEq(gen.createUniqueIdentifier("foo"), "foo")
    assertEq(gen.createUniqueIdentifier("foo"), "foo_1")
    assertEq(gen.createUniqueIdentifier("foo"), "foo_2")
    assertEq(gen.createUniqueIdentifier("foo"), "foo_3")
  }

  test("Subcontext Unique Counter") {
    assertEq(sub.createUniqueIdentifier("foo"), "foo")
    assertEq(sub.createUniqueIdentifier("foo"), "foo_1")
    assertEq(sub.createUniqueIdentifier("foo"), "foo_2")
    assertEq(sub.createUniqueIdentifier("foo"), "foo_3")
  }

  test("Enclosing Context Common Unique Counter") {
    assertEq(gen.createUniqueIdentifier("foo"), "foo")
    assertEq(gen.createUniqueIdentifier("foo"), "foo_1")
    assertEq(sub.createUniqueIdentifier("foo"), "foo_2")
    assertEq(sub.createUniqueIdentifier("foo"), "foo_3")
    assertEq(subsub.createUniqueIdentifier("foo"), "foo_4")
    assertEq(subsub.createUniqueIdentifier("foo"), "foo_5")
  }

  test("Subcontext Common Unique Counter") {
    assertEq(sub.createUniqueIdentifier("foo"), "foo")
    assertEq(gen.createUniqueIdentifier("foo"), "foo_1")
    assertEq(sub.createUniqueIdentifier("foo"), "foo_2")
    assertEq(subsub.createUniqueIdentifier("foo"), "foo_3")
    assertEq(sub.createUniqueIdentifier("foo"), "foo_4")
    assertEq(gen.createUniqueIdentifier("foo"), "foo_5")
  }

  test("Independent Subcontexts") {
    assertEq(sub.createUniqueIdentifier("foo"), "foo")
    assertEq(sub2.createUniqueIdentifier("foo"), "foo")
    assertEq(subsub.createUniqueIdentifier("bar"), "bar")
    assertEq(subsub2.createUniqueIdentifier("bar"), "bar")
    assertEq(sub2sub.createUniqueIdentifier("bar"), "bar")
  }

  test("Partially Independent Subcontexts") {
    assertEq(sub.createUniqueIdentifier("foo"), "foo")
    sub2.createUniqueIdentifier("foo")
    for (i <- 1 until 10) {
      assertEq(sub2.createUniqueIdentifier("foo"), "foo_" + i)
    }
    sub2.createUniqueIdentifier("foo_10")
    assertEq(gen.createUniqueIdentifier("foo"), "foo_11")
    assertEq(subsub.createUniqueIdentifier("bar"), "bar")
    assertEq(subsub2.createUniqueIdentifier("bar"), "bar")
    assertEq(sub2sub.createUniqueIdentifier("bar"), "bar")
    assertEq(sub2sub.createUniqueIdentifier("bar"), "bar_1")
    assertEq(sub2.createUniqueIdentifier("bar"), "bar_2")
    assertEq(gen.createUniqueIdentifier("bar"), "bar_3")
  }

  test("Faked Counters") {
    assertEq(gen.createUniqueIdentifier("foo"), "foo")
    assertEq(gen.createUniqueIdentifier("foo_1"), "foo_1")
    assertEq(gen.createUniqueIdentifier("foo_2"), "foo_2")
    assertEq(gen.createUniqueIdentifier("foo"), "foo_3")
  }

  test("Faked Counters in Enclosing Contexts") {
    assertEq(gen.createUniqueIdentifier("foo"), "foo")
    assertEq(gen.createUniqueIdentifier("foo_1"), "foo_1")
    assertEq(gen.createUniqueIdentifier("foo_2"), "foo_2")
    assertEq(sub.createUniqueIdentifier("foo_4"), "foo_4")
    assertEq(subsub.createUniqueIdentifier("foo"), "foo_3")
  }

  test("Faked Counters in Subcontexts") {
    assertEq(sub.createUniqueIdentifier("foo"), "foo")
    assertEq(sub2.createUniqueIdentifier("foo_1"), "foo_1")
    assertEq(sub2sub.createUniqueIdentifier("foo"), "foo")
    assertEq(subsub.createUniqueIdentifier("foo_2"), "foo_2")
    assertEq(subsub2.createUniqueIdentifier("foo_4"), "foo_4")
    assertEq(gen.createUniqueIdentifier("foo"), "foo_3")
  }
}
