// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.testing

import java.nio.file._
import collection.mutable
import org.scalatest.{BeforeAndAfterAllConfigMap, ConfigMap}
import viper.silver.verifier._
import viper.silver.ast.{SourcePosition, TranslatedPosition}
import viper.silver.frontend.Frontend
import viper.silver.utility.TimingUtils

/** A test suite for verification toolchains that use Viper. */
abstract class SilSuite extends AnnotationBasedTestSuite with BeforeAndAfterAllConfigMap {

  /** The list of verifiers to be used. Should be overridden by a lazy val
    * if the verifiers need to access the config map provided by ScalaTest.
    */
  def verifiers: Seq[Verifier]

  /** The frontend to be used. */
  def frontend(verifier: Verifier, files: Seq[Path]): Frontend

  /** The list of projects under the test.
    *
    * Silver is always included - this means that e.g. IgnoreFile annotations
    * for Silver project will cause the file to be ignored by all verifiers
    */
  def projectInfo: ProjectInfo = new ProjectInfo(List("Silver"))

  /** Populated by splitting the (key, values) in `configMap` (which is
    * expected to be non-null) into (prefix, actual key, value) triples such
    * that each prefix maps to a map from actual keys to values. A colon (':')
    * is used as the split point for splitting a key into (prefix, actual key)
    * pairs. If not prefix (colon) is given, `defaultKeyPrefix` is used as the
    * prefix. Each key in `configMap` may have at least one colon.
    */
  lazy val prefixSpecificConfigMap: Map[String, Map[String, Any]] =
  splitConfigMap(configMap)

  /** Invoked by ScalaTest before any test of the current suite is run.
    * Starts all verifiers specified by `verifiers`.
    *
    * @param configMap The config map provided by ScalaTest.
    */
  override def beforeAll(configMap: ConfigMap) {
    this.configMap = configMap
    verifiers foreach (_.start())
  }

  /** Invoked by ScalaTest after all tests of the current suite have been run.
    * Stops all verifiers specified by `verifiers`.
    */
  override def afterAll(configMap: ConfigMap) {
    verifiers foreach (_.stop())
  }

  def systemsUnderTest: Seq[SystemUnderTest] =
    verifiers.map(VerifierUnderTest)

  val defaultKeyPrefix = ""

  /** See description of `prefixSpecificConfigMap`.
    *
    * @param configMap The config map provided by ScalaTest.
    * @return A map mapping key prefixes to (key, value) pairs.
    */
  protected def splitConfigMap(configMap: Map[String, Any]): Map[String, Map[String, Any]] = {
    val prefixSpecificConfigMap = mutable.HashMap[String, mutable.HashMap[String, Any]]()

    configMap foreach {
      case (potentialKey, value) =>
        val (prefix, key) =
          potentialKey.split(':') match {
            case Array(_key) => (defaultKeyPrefix, _key)
            case Array(_prefix, _key) => (_prefix, _key)
            case _ => sys.error(s"Unexpected key $potentialKey in config map $configMap. Keys are expected to contain at most one colon (':').")
          }

        prefixSpecificConfigMap.getOrElseUpdate(prefix, mutable.HashMap()).update(key, value)
    }

    prefixSpecificConfigMap.mapValues(_.toMap).toMap
  }

  private case class VerifierUnderTest(verifier: Verifier)
    extends SystemUnderTest with TimingUtils {

    val projectInfo: ProjectInfo = SilSuite.this.projectInfo.update(verifier.name)

    def run(input: AnnotatedTestInput): Seq[AbstractOutput] = {
      val fe = frontend(verifier, input.files)
      val tPhases = fe.phases.map { p =>
        formatTime(time(p.action)._2) + " (" + p.name + ")"
      }.mkString(", ")
      info(s"Verifier used: ${verifier.name} ${verifier.version}.")
      info(s"Time required: $tPhases.")
      val actualErrors = fe.result match {
        case Success => Nil
        case Failure(es) => es collect {
          case e: AbstractVerificationError =>
            e.transformedError()
          case rest: AbstractError => rest
        }
      }
      actualErrors.map(SilOutput)
    }
  }

}

/**
  * Simple adapter for outputs produced by the Viper toolchain, i.e.,
  * [[viper.silver.verifier.AbstractError]]s.
  *
  * The advantage is that it allows [[viper.silver.testing.AbstractOutput]]
  * to be independent from the Viper AST.
  *
  * @param error the error produced by the Viper toolchain.
  */
case class SilOutput(error: AbstractError) extends AbstractOutput {
  def isSameLine(file: Path, lineNr: Int): Boolean = error.pos match {
    case p: SourcePosition => lineNr == p.line
    case p: TranslatedPosition => file == p.file && lineNr == p.line
    case _ => false
  }

  def fullId: String = error.fullId

  override def toString: String = error.toString
}

