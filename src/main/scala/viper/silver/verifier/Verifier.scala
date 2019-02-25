// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.verifier

import viper.silver.ast.Program
import viper.silver.components.LifetimeComponent

/** An abstract class for verifiers of Viper programs.
  *
  * The lifetime of a verifier is as follows.  After the object has been created, `commandLineArgs` is called
  * at most once to set the command line arguments.  Similarly for `debugInfo` which is also called
  * at most once, either before or after `commandLineArgs`.
  * Afterwards, one or more calls to `verify` follow.
  *
  * RFC: [Malte] If we made this an abstract class, then `commandLineArgs` and `debugInfo` could
  *      be constructor arguments and we wouldn't have to impose a protocol on clients.
  *
  * RFC: [Malte] If we renamed method `verify` to something more generic, e.g., `handle`,
  *      then this trait could be generalised from `Verifier` to `SilProgramHandler` or
  *      `SilTool`.
  *
  * RFC: [Malte] In order to facilitate creating verifier instances by reflection, e.g.,
  *      by a frontend that has an option such as "--backend viper.silicon.Silicon",
  *      telling it to run the specified backend, we should prescribe a standard
  *      constructor, e.g., Verifier().
  */
trait Verifier extends LifetimeComponent {

  /** The name of this verifier (all-lowercase, to be used to uniquely identify this verifier). */
  def name: String

  /**
   * Returns the version of the verifier. This should be the main version only, e.g., "1.0.1"
   * or "1.0.1-SNAPSHOT".
   */
  def version: String

  /**
   * Returns the version of the verifier, including any information that could help identifying
   * the build, e.g., the code revision. This version is intended to be used for debugging.
   */
  def buildVersion: String

  /** Returns the copyright string of this verifier, e.g., "(c) 2013 Name" */
  def copyright: String

  /** Returns the signature of the verifier. */
  def signature: String = s"$name $version"

  /**
   * Set some debug information from the calling part of the system.
   *
   * Key-value pairs of information that could help during debugging. For example,
   * the full command line that was used to (indirectly, for instance, via a translator) start the
   * verifier.
   */
  def debugInfo(info: Seq[(String, Any)])

  /**
   * Returns the dependencies.  A dependency could be any library or stand-alone
   * tool that this verifier relies on, either directly or indirectly.  Typically only other
   * tools in the verification tool-chain are included here which can easily influence the
   * verification outcome.
   */
  def dependencies: Seq[Dependency]

  /** Set the command-line arguments to be used in this verifier.
    * Is expected to be called before `start`.
    */
  def parseCommandLine(args: Seq[String])

  /** Starts the verifier. Afterwards, a series of calls to `verify` is expected,
    * finally followed by a call to `stop`.
    * Is expected to be preceded by a call to `parseCommandLine`.
    */
  def start()

  /** Verifies a given Viper program and returns a sequence of ''verification errors''.
    * Is expected to be preceded by a call to `start`.
    *
    * @param program The program to be verified.
    * @return The verification result.
    */
  def verify(program: Program): VerificationResult

  /** Stops the verifier. The behaviour of subsequent calls to `start` or `verify`
    * is unspecified.
    */
  def stop()
}

/**
 * Empty verifier that can be used as a placeholder for tests if the verification never actually gets called.
 */
class NoVerifier extends Verifier {
  val name = "noverifier"
  val version = "0.0.0"
  val buildVersion = ""
  val copyright = ""
  val dependencies = Nil

  def debugInfo(info: Seq[(String, Any)]) {}
  def parseCommandLine(args: Seq[String]) {}

  def start() = {}

  /** Is not implemented and should never be called. */
  def verify(program: Program) = ???

  def stop() = {}
}

/** A description of a dependency of a verifier. */
trait Dependency {

  /** The name of the dependency. */
  def name: String

  /** The version of this dependency. */
  def version: String

  /** The location of this dependency.  Typically a path. */
  def location: String
}

case class DefaultDependency(name: String, version: String, location: String) extends Dependency
