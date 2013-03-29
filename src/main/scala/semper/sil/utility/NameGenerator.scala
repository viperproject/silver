package semper.sil.utility

import semper.sil.ast.utility.Consistency
import util.matching.Regex

/**
 * A trait to generate unique names.
 */
trait NameGenerator {

  /**
   * The string used to separate the preferred identifier from the number postfix.
   */
  def separator: String

  /**
   * A regular expression that matches any character allowed as a first char in a valid
   * identifier.
   */
  def firstCharacter: Regex

  /**
   * A regular expression that matches the characters allowed (except in the first position).
   */
  def otherCharacter: Regex

  private val lock = new Object

  /**
   * Returns a different string every time it is called. If possible, it
   * returns the input string, otherwise, it appends a number at the end.
   * If the input is a valid SIL identifier, the output is also a valid SIL identifier.
   * Calling this method directly would not be thread safe.
   */
  // TODO: Contexts
  def createUnique(s: String) = lock.synchronized {
    if (!identCounters.contains(s)) {
      identCounters.put(s, 0)
      s
    } else {
      var counter = identCounters(s) + 1
      var newS = s + separator + counter.toString
      while (identCounters.contains(newS)) {
        counter += 1
        newS = s + separator + counter.toString
      }
      identCounters.put(newS, counter)
      newS
    }
  }

  private val identCounters = collection.mutable.HashMap[String, Int]()

  /**
   * Creates a different identifier every time it is called.
   */
  def createUniqueIdentifier(s: String) = createUnique(createIdentifier(s))

  /**
   * Takes an arbitrary string and returns a valid identifier that
   * resembles that string. Special characters are replaced or removed.
   */
  def createIdentifier(input: String) = {
    if (input.isEmpty) {
      "i"
    } else {
      val result = new StringBuilder
      // If the first letter of `string` is allowed inside, but not at the beginning, put an additional i at the beginning.
      val first = input.head.toString
      if (otherCharacter.findFirstIn(first).isDefined && !firstCharacter.findFirstIn(first).isDefined) {
        result append "i"
      }
      input foreach {
        c =>
          if (otherCharacter.findFirstIn(c.toString).isDefined) {
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
  }

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
    'ω' -> "omega",
    '+' -> "plus",
    '-' -> "minus",
    '*' -> "times",
    '/' -> "divided",
    '%' -> "mod",
    '!' -> "bang"
  )
}
