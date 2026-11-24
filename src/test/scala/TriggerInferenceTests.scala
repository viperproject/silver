// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

import java.nio.file.Files

import TestHelpers.MockSilFrontend
import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast._
import viper.silver.ast.utility.Triggers.{NotInTriggerInfo, TriggerGeneration, TriggerGenerationWithAddAndSubtract}
import viper.silver.plugin.standard.adt.{Adt, AdtConstructor, AdtConstructorApp, AdtType}
import viper.silver.plugin.standard.adt.encoding.AdtEncoder

/** Tests the triggers that Silver infers for programs with `@notInTrigger()` annotations. */
class TriggerInferenceTests extends AnyFunSuite {

  /** The inferred trigger sets of the quantifiers that the methods of `program` inhale */
  private def inferredTriggers(program: Program, annotations: Boolean): Seq[Seq[String]] = {
    val generator = new TriggerGeneration(if (annotations) Some(program) else None)
    program.methods.flatMap(_.deepCollect { case Inhale(q: Forall) => q })
      .map(_.autoTriggerWith(generator).triggers.map(_.exps.mkString(", ")))
  }

  /** Translates `source` and encodes its ADTs */
  private def translate(source: String): Program = {
    val file = Files.createTempFile("trigger-inference", ".vpr")
    try {
      Files.writeString(file, source)
      val frontend = new MockSilFrontend
      frontend.translate(file) match {
        case (Some(p), Seq()) => frontend.plugins.beforeVerify(p).get
        case (_, errors) => fail(s"Could not translate the test program: ${errors.mkString(", ")}")
      }
    } finally {
      Files.delete(file)
    }
  }

  /** The inferred trigger sets of the quantifiers that the methods of the program `source` inhale. If `annotations`
    * is false, the generator does not see the program and ignores annotations.
    */
  private def inferredTriggers(source: String, annotations: Boolean = true): Seq[Seq[String]] =
    inferredTriggers(translate(source), annotations)

  private val functions =
    """function f(i: Int): Bool
      |function g(i: Int): Int
      |function h(i: Int): Bool
      |""".stripMargin

  test("A @notInTrigger() function is treated like a built-in operator") {
    val source = functions +
      """@notInTrigger()
        |function add(i: Int, j: Int): Int
        |
        |method test() {
        |  inhale forall i: Int :: f(add(i, 1)) && h(i)
        |  inhale forall i: Int :: f(add(g(i), 1))
        |  inhale forall i: Int :: add(i, 1) > 0
        |}
        |""".stripMargin
    assert(inferredTriggers(source) == Seq(Seq("h(i)"), Seq("g(i)"), Seq()))
    assert(inferredTriggers(source, annotations = false) ==
      Seq(Seq("f(add(i, 1))", "h(i)"), Seq("f(add(g(i), 1))"), Seq("add(i, 1)")))
  }

  test("A Bool-valued @notInTrigger() function (e.g. a comparison) is not a trigger term either") {
    val source = functions +
      """@notInTrigger()
        |function lt(i: Int, j: Int): Bool
        |
        |method test(n: Int) {
        |  inhale forall i: Int :: lt(i, n) ==> f(i)
        |  inhale forall i: Int :: lt(g(i), n) ==> f(i)
        |  inhale forall i: Int :: f(i) == lt(g(i), n)
        |}
        |""".stripMargin
    assert(inferredTriggers(source) == Seq(Seq("f(i)"), Seq("g(i)", "f(i)"), Seq("f(i)", "g(i)")))
    assert(inferredTriggers(source, annotations = false) ==
      Seq(Seq("lt(i, n)", "f(i)"), Seq("lt(g(i), n)", "f(i)"), Seq("f(i)", "lt(g(i), n)")))
  }

  test("The annotation applies to domain functions and to ADT constructors and their destructors") {
    val source = functions +
      """domain Ops {
        |  @notInTrigger()
        |  function plus(i: Int, j: Int): Int
        |}
        |
        |adt Wrapper {
        |  @notInTrigger() wrap(value: Int)
        |}
        |
        |method test() {
        |  inhale forall i: Int :: f(plus(i, 1)) && h(i)
        |  inhale forall i: Int :: f(wrap(i).value) && h(i)
        |}
        |""".stripMargin
    assert(inferredTriggers(source) == Seq(Seq("h(i)"), Seq("h(i)")))
    assert(inferredTriggers(source, annotations = false) ==
      Seq(Seq("f(plus(i, 1))", "h(i)"), Seq("f(get_Wrapper_value(wrap(i)))", "h(i)")))
  }

  test("Terms under a let-binding are found, unless they use a variable bound to a forbidden expression") {
    val source = functions +
      """method test() {
        |  inhale forall i: Int :: (let j == (i + 1) in f(i) && h(j))
        |  inhale forall i: Int :: (let j == (g(i)) in h(j))
        |}
        |""".stripMargin
    assert(inferredTriggers(source) == Seq(Seq("f(i)"), Seq("h(g(i))")))
  }

  test("Different generators do not reuse each other's fresh variables") {
    val program = translate(
      """function f(i: Int, b: Bool): Bool
        |function h(j: Int, b: Bool): Bool
        |
        |method test() {
        |  inhale forall i: Int :: f(i + 1, i > 0) && (forall j: Int :: h(j, j > 0))
        |}
        |""".stripMargin)
    val quantifier = program.methods.flatMap(_.deepCollect { case Inhale(q: Forall) => q }).head
    /* As Silicon does: the inner quantifier first, with one generator, and then the outer one, with another */
    val body = quantifier.exp.transform { case inner: Forall => inner.autoTriggerWith(new TriggerGeneration()) }
    val outer = Forall(quantifier.variables, Nil, body)().autoTriggerWith(new TriggerGenerationWithAddAndSubtract())
    assert(outer.triggers.nonEmpty)
  }

  test("The annotation is read from the info of members of a program that is built as an AST, without parsing") {
    assert(inferredTriggers(AstBuiltTriggerProgram.encoded, annotations = true) ==
      AstBuiltTriggerProgram.expectedTriggers)
  }
}

/** A program with `@notInTrigger()` annotations that is built as an AST (as e.g. Prusti does), not parsed: the
  * annotations are only the `AnnotationInfo`s in the `info` of a function, a domain function and an ADT constructor
  * (whose destructors it also covers). Its method inhales `quantifiers`, for which `expectedTriggers` should be
  * inferred.
  */
object AstBuiltTriggerProgram {
  private val i = LocalVarDecl("i", Int)()
  private val j = LocalVarDecl("j", Int)()
  private def int(n: Int) = IntLit(n)()

  /* The annotation next to other information, including another AnnotationInfo */
  private val add = Function("add", Seq(i, j), Int, Nil, Nil, None)(
    info = ConsInfo(AnnotationInfo(Map("other" -> Nil)), NotInTriggerInfo))
  private val f = Function("f", Seq(i), Bool, Nil, Nil, None)()
  private val h = Function("h", Seq(i), Bool, Nil, Nil, None)()
  private def call(function: Function, args: Exp*) = FuncApp(function, args)()

  private val lt = DomainFunc("lt", Seq(i, j), Bool)(info = NotInTriggerInfo, domainName = "Ops")
  private val ops = Domain("Ops", Seq(lt), Nil)()
  private def less(a: Exp, b: Exp) = DomainFuncApp(lt, Seq(a, b), Map.empty[TypeVar, Type])()

  private val wrapperType = AdtType("Wrapper", Map.empty[TypeVar, Type])(Nil)
  private val wrapConstructor =
    AdtConstructor("wrap", Seq(LocalVarDecl("value", Int)()))(NoPosition, NotInTriggerInfo, wrapperType, "Wrapper",
                                                              NoTrafos)
  private val wrapper = Adt("Wrapper", Seq(wrapConstructor))()
  private def wrap(e: Exp) = AdtConstructorApp(wrapConstructor, Seq(e), Map.empty[TypeVar, Type])()

  private def forall(body: Exp) = Forall(Seq(i), Nil, body)()

  val quantifiers: Seq[Forall] = Seq(
    /* forall i: Int :: f(add(i, 1)) && h(i) */
    forall(And(call(f, call(add, i.localVar, int(1))), call(h, i.localVar))()),
    /* forall i: Int :: lt(i, 5) ==> f(i) */
    forall(Implies(less(i.localVar, int(5)), call(f, i.localVar))()),
    /* forall i: Int :: wrap(i) == wrap(0) || h(i) */
    forall(Or(EqCmp(wrap(i.localVar), wrap(int(0)))(), call(h, i.localVar))()),
    /* forall i: Int :: f(add(i, 1)) && h(i + 1): has triggers only if `+` is admitted (see
     * Triggers.TriggerGenerationWithAddAndSubtract) */
    forall(And(call(f, call(add, i.localVar, int(1))), call(h, Add(i.localVar, int(1))()))()))

  val expectedTriggers: Seq[Seq[String]] = Seq(Seq("h(i)"), Seq("f(i)"), Seq("h(i)"), Seq())

  val program: Program =
    Program(Seq(ops), Nil, Seq(add, f, h), Nil,
            Seq(Method("test", Nil, Nil, Nil, Nil, Some(Seqn(quantifiers.map(Inhale(_)()), Nil)()))()),
            Seq(wrapper))()

  /** The program after the ADT plugin's encoding, which happens before verification */
  lazy val encoded: Program = new AdtEncoder(program).encode(isTerminationPluginActive = false)
}
