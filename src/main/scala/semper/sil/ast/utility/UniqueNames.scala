package semper.sil.ast.utility

import semper.sil.parser.Parser
import scala.actors.Actor

object UniqueNames {
  
  /**
   * Takes an arbitrary string and returns a valid identifier that
   * resembles that string. Special characters are deleted or removed.
   */
  def createIdentifier(input: String) = {
    if (input.isEmpty) {
      "i"
    } else {
      var result = new StringBuilder
      val firstLetter = Parser.identFirstLetter.r
      val otherLetter = Parser.identOtherLetter.r
      // If the first letter of `string` is allowed inside, but not at the beginning, put an additional i at the beginning.
      val first = input.head.toString 
      if (otherLetter.findFirstIn(first).isDefined && !firstLetter.findFirstIn(first).isDefined) {
        result append "i"
      }
      input foreach { c =>
        if (otherLetter.findFirstIn(c.toString).isDefined) {
          result append c
        } else if (replacableLetters.contains(c)) {
          result append replacableLetters(c)
        }
      }
      if (result.isEmpty) {
        "i"
      } else {
        result.result
      }
    }
  } ensuring { Consistency.validIdentifier(_) }
  
  /** Special letters that can be replaced with a specific string inside identifiers */
  lazy val replacableLetters = Map(
      'Α' -> "Alpha",
      'Β' -> "Beta",
      'Γ' -> "Gamma",
      'Δ' -> "Delta",
      'Ε' -> "Epsilon",
      'Ζ' -> "Zeta",
      'Η' -> "Eta",
      'Θ' -> "Theta",
      'Ι' -> "Iota",
      'Κ' -> "Kappa",
      'Λ' -> "Lambda",
      'Μ' -> "My",
      'Ν' -> "Ny",
      'Ξ' -> "Xi",
      'Ο' -> "Omikron",
      'Π' -> "Pi",
      'Ρ' -> "Rho",
      'Σ' -> "Sigma",
      'Τ' -> "Tau",
      'Υ' -> "Ypsilon",
      'Φ' -> "Phi",
      'Χ' -> "Chi",
      'Ψ' -> "Psi",
      'Ω' -> "Omega",
      'α' -> "alpha",
      'β' -> "beta",
      'γ' -> "gamma",
      'δ' -> "delta",
      'ε' -> "epsilon",
      'ζ' -> "zeta",
      'η' -> "eta",
      'θ' -> "theta",
      'ι' -> "iota",
      'κ' -> "kappa",
      'λ' -> "lambda",
      'μ' -> "my",
      'ν' -> "ny",
      'ξ' -> "xi",
      'ο' -> "omikron",
      'π' -> "pi",
      'ρ' -> "rho",
      'ς' -> "varsigma",
      'σ' -> "sigma",
      'τ' -> "tau",
      'υ' -> "ypsilon",
      'φ' -> "phi",
      'χ' -> "chi",
      'ψ' -> "psi",
      'ω' -> "omega"
      )
}