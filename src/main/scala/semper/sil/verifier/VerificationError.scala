package semper.sil.verifier

/** A case class to describe an error during the verification of a SIL program.
  *
  * @author Stefan Heule
  */
sealed case class VerificationError(id: String, lineNr: Int)
