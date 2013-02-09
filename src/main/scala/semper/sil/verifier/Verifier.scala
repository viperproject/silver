
package semper.sil.verifier

import semper.sil.ast.Program

/** An abstract class for verifiers of SIL programs.
  *
  * @param options The command-line arguments to be used in this verifier.
  * @author Stefan Heule
  */
abstract class Verifier(options: Seq[String] = Nil) {

  /** The name of this verifier (all-lowercase, to be used to uniquely identify this verifier). */
  def name: String

  /** Returns the version of the verifier. */
  def version: String

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
