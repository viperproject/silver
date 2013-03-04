
package semper.sil.verifier

import semper.sil.ast.Program

/** An abstract class for verifiers of SIL programs.
  *
  * @author Stefan Heule
  */
abstract class Verifier() {

  /** Set the command-line arguments to be used in this verifier. */
  def commandLineArgs(options: Seq[String])

  /** The name of this verifier (all-lowercase, to be used to uniquely identify this verifier). */
  def name: String

  /** Returns the version of the verifier. */
  def version: String

  /** Returns the copyright string of this verifier, e.g., "(c) 2013 Name" */
  def copyright: String

  /** Returns the versions of its dependencies.
    *
    * @return A sequence of pairs `(toolName, version)`.
    */
  def dependencyVersions: Seq[(String, String)]

  /** Verifies a given SIL program and returns a sequence of ''verification errors''.
    *
    * @param program The program to be verified.
    * @return The verification result.
    */
  def verify(program: Program): VerificationResult
}
