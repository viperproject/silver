package semper.sil.ast.utility

import semper.sil.parser.Parser
import scala.actors.Actor
import scala.collection.mutable.HashMap

object UniqueNames {
  
  private val uniqueActor = new UniqueActor  

  /**
   * Returns a different string every time it is called. If possible, it
   * returns the input string, otherwise, it appends a number at the end.
   * If the input is a valid SIL identifier, the output is also a valid SIL identifier.
   * This is thread safe.
   * TODO Contexts
   */
  def createUnique(s: String) = {
    val res = uniqueActor !? s
    res match {
      case i: String => i
      case _ => throw new RuntimeException("Invalid response " + res + "from UniqueActor")
    }   
  }
  
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

class UniqueActor extends Actor {
  def act {
    receive {
      case s: String => reply(createUnique(s))
    }
  }
  
  private val identCounters: HashMap[String, Int] = HashMap()
  
  val separator = "_"
   
  /**
   * Returns a different string every time it is called. If possible, it
   * returns the input string, otherwise, it appends a number at the end.
   * If the input is a valid SIL identifier, the output is also a valid SIL identifier.
   * Calling this method directly would not be thread safe.
   */
  private def createUnique(s: String) = {
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
}