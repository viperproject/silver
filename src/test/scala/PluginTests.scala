// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

import java.nio.file.Paths
import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast.{LocalVar, Perm, Program}
import viper.silver.frontend.{SilFrontend, SilFrontendConfig}
import viper.silver.parser.{PDelimited, PGrouped, PIdnDef, PKw, PPredicate, PProgram, PReserved}
import viper.silver.plugin.{SilverPlugin, SilverPluginManager}
import viper.silver.reporter.{Reporter, StdIOReporter}
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.FeatureUnsupported
import viper.silver.verifier._
import viper.silver.ast.NoPosition

import scala.annotation.unused

trait TestPlugin {
  def test(): Boolean = true
}

trait FakeResult {
  def result(): VerificationResult = Success
}

class TestPluginImport extends SilverPlugin with TestPlugin {
  var calledFalse = false
  var calledTrue = false

  override def beforeParse(input: String, isImported: Boolean): String = {
    if (isImported) {
      assert(!calledTrue)
      calledTrue = true
    } else {
      assert(!calledFalse)
      calledFalse = true
    }
    input
  }

  override def test(): Boolean = calledTrue && calledFalse
}

class TestPluginReportError extends SilverPlugin {
  var error: Internal = _

  override def beforeMethodFilter(input: Program): Program = {
    error = Internal(FeatureUnsupported(input, "Test"))
    reportError(error)
    input
  }

  override def beforeVerify(input: Program): Program = {
    assert(false)
    input
  }

  override def beforeFinish(input: VerificationResult): VerificationResult = {
    input match {
      case Success => assert(false)
      case Failure(errs) => assert(errs.contains(error))
    }
    input
  }
}

class TestPluginAllCalled extends SilverPlugin with TestPlugin {

  var parse = false
  var resolve = false
  var translate = false
  var filter = false
  var verify = false
  var finish = false

  override def beforeParse(input: String, isImported: Boolean): String = {
    parse = true
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    assert(parse)
    resolve = true
    input
  }

  override def beforeTranslate(input: PProgram): PProgram = {
    assert(parse && resolve)
    translate = true
    input
  }

  override def beforeMethodFilter(input: Program): Program = {
    assert(parse && resolve && translate)
    filter = true
    input
  }

  override def beforeVerify(input: Program): Program = {
    assert(parse && resolve && translate && filter)
    verify = true
    input
  }

  override def beforeFinish(input: VerificationResult): VerificationResult = {
    assert(parse && resolve && translate && filter && verify)
    finish = true
    input
  }

  override def test(): Boolean = parse && resolve && translate && filter && verify && finish
}

class TestPluginAddPredicate extends SilverPlugin {

  override def beforeResolve(input: PProgram): PProgram = {
    val p = (NoPosition, NoPosition)
    PProgram(
      input.imported,
      input.members :+ PPredicate(Seq(), PReserved.implied(PKw.Predicate), PIdnDef("testPredicate")(p), PGrouped.impliedParen(PDelimited.empty), None)(p),
    )(input.pos, input.localErrors, input.offsets, input.rawProgram)
  }

  /** Called after methods are filtered but before the verification by the backend happens.
    *
    * @param input AST
    * @return Modified AST
    */
  override def beforeVerify(input: Program): Program = {
    assert(input.predicates.exists(p => p.name == "testPredicate"))
    input
  }
}

// ATG: After introducing `PluginAwareReporter` this test became rather trivial.
class TestPluginMapErrors extends SilverPlugin with TestPlugin with FakeResult {

  var error1: Internal = Internal(FeatureUnsupported(LocalVar("test1", Perm)(), "Test1"))
  var error2: Internal = Internal(FeatureUnsupported(LocalVar("test2", Perm)(), "Test2"))
  var finish = false

  override def mapVerificationResult(@unused program: Program, input: VerificationResult): VerificationResult = {
    input match {
      case Success =>
//        println(">>> detected VerificationResult is Success")
        assert(false)
        input
      case Failure(errors) =>
//        println(s">>> detected VerificationResult is Failure: ${errors.toString()}")
        assert(errors.contains(error1))
        Failure(Seq(error2))
    }
  }

  override def beforeFinish(input: VerificationResult): VerificationResult = {
    finish = true
    input match {
      case Success =>
//        println("]]] detected VerificationResult is Success")
        assert(false)
      case Failure(errors) =>
//        println(s"]]] detected VerificationResult is Failure: ${errors.toString()}")
        assert(!errors.contains(error1))
        assert(errors.contains(error2))
    }
    input
  }

  override def test(): Boolean = finish

  override def result(): VerificationResult = Failure(Seq(error1))
}

class TestPluginMapVsFinish extends SilverPlugin with TestPlugin {

  var error: Internal = _
  var mapping = false
  var finish = false

  override def beforeResolve(input: PProgram): PProgram = {
    error = Internal(FeatureUnsupported(LocalVar("test", Perm)(), "Test"))
    reportError(error)
    input
  }

  override def beforeTranslate(input: PProgram): PProgram = {
    assert(false)
    input
  }

  override def mapVerificationResult(@unused program: Program, input: VerificationResult): VerificationResult = {
    assert(!finish)
    input
  }

  override def beforeFinish(input: VerificationResult): VerificationResult = {
    finish = true
    input match {
      case Success => assert(false)
      case Failure(errors) =>
        assert(errors.contains(error))
    }
    input
  }

  override def test(): Boolean = !mapping && finish
}

class PluginTests extends AnyFunSuite {
  val inputfile = "plugintests/plugininput.vpr"
  val plugins = Seq(
    "TestPluginImport",
    "TestPluginReportError",
    "TestPluginAllCalled",
    "TestPluginAddPredicate",
    "TestPluginMapErrors",
    "TestPluginMapVsFinish"
  )

  var result: VerificationResult = Success

  def testOne(plugin: String): Unit ={
    val resource = getClass.getResource(inputfile)
    assert(resource != null, s"File $inputfile not found")
    val file = Paths.get(resource.toURI)
    val frontend = new MockPluginFrontend
    val instance = SilverPluginManager.resolve(plugin)
    assert(instance.isDefined)
    result = instance.get match {
      case p: FakeResult => p.result()
      case _ => Success
    }
    frontend.execute(Seq("--plugin", plugin, file.toString))
    assert(frontend.plugins.plugins.size == 1 + frontend.defaultPluginCount)
    frontend.plugins.plugins.foreach {
      case p: TestPlugin => assert(p.test(), p.getClass.getName)
      case _ =>
    }
  }

  plugins.foreach(p => test(p)(testOne(p)))

  class MockPluginFrontend extends SilFrontend {

    protected var instance: MockPluginVerifier = _

    override def createVerifier(fullCmd: String): Verifier = {
      instance = new MockPluginVerifier
      instance
    }

    override def configureVerifier(args: Seq[String]): SilFrontendConfig = {
      instance.parseCommandLine(args)
      instance.config
    }
  }

  class MockPluginVerifier extends Verifier {

    private var _config: MockPluginConfig = _

    def config: MockPluginConfig = _config

    override def name: String = "MockPluginVerifier"

    override def version: String = "3.14"

    override def buildVersion: String = "2.71"

    override def copyright: String = "(c) Copyright ETH Zurich 2012 - 2021"

    override def debugInfo(info: Seq[(String, Any)]): Unit = {}

    override def dependencies: Seq[Dependency] = Seq()

    override def parseCommandLine(args: Seq[String]): Unit = {
      _config = new MockPluginConfig(args)
    }

    override def start(): Unit = {}

    override def verify(program: Program): VerificationResult = {
      result
    }

    override def stop(): Unit = {}

    override def reporter: Reporter = StdIOReporter()
  }

  class MockPluginConfig(args: Seq[String]) extends SilFrontendConfig(args, "MockPluginVerifier"){
    verify()
  }
}
