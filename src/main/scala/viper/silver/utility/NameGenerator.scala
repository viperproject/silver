// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import util.matching.Regex

/**
 * Interface for a class that can generate unique names.
 */
trait NameGenerator {

  /**
   * Creates a different identifier every time it is called.
   */
  def createUniqueIdentifier(s: String): String

  /**
   * Returns a different string every time it is called. If possible, it
   * returns the input string, otherwise, it appends a number at the end.
   * If the input is a valid identifier, the output is also a valid identifier.
   * Calling this method directly would not be thread safe.
   */
  def createUnique(s: String): String

  /**
   * Takes an arbitrary string and returns a valid identifier that
   * resembles that string. Special characters are replaced or removed.
   */
  def createIdentifier(s: String): String

  /**
   * Returns a sub context for names. The names within that context can not conflict with
   * names in the global context, but there may be several subcontexts with names which
   * conflict whith each other.
   */
  def createSubContext(): NameGenerator

}

/**
 * Default Implementation for the name generator.
 */
trait DefaultNameGenerator extends NameGenerator {
  val globalContext = new NameContext()

  /**
   * The string used to separate the preferred identifier from the number postfix.
   */
  def separator: String

  /**
   * The default identifier that is used in case of empty identifiers.
   */
  def defaultIdent = "v"

  /**
   * A regular expression that matches any character allowed as a first char in a valid
   * identifier.
   */
  def firstCharacter: Regex

  /**
   * A regular expression that matches the characters allowed (except in the first position).
   */
  def otherCharacter: Regex

  /**
   * A set of names which are forbidden as valid identifiers.
   */
  def reservedNames: Set[String]

  /** Special letters that can be replaced with a specific string inside identifiers */
  lazy val replaceableLetters = Map(
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
    '!' -> "bang",
    '<' -> "less" ,
    '>' -> "greater",
    '=' -> "eq")

  def createUniqueIdentifier(s: String) = globalContext.createUniqueIdentifier(s)

  def createUnique(s: String) = globalContext.createUnique(s)

  /**
   * A context inside which the names have to be unique. They also have to be unique within all enclosing contexts,
   * but there might be independent contexts which contain the same names.
   */
  class NameContext(enclosingContexts: List[NameContext] = Nil) extends NameGenerator {
    private var directSubContexts = List[NameContext]()

    private val identCounters = collection.mutable.HashMap[String, Int]()

    private val contexts = this :: enclosingContexts

    private def subContexts: List[NameContext] = directSubContexts ++ directSubContexts.flatMap(_.subContexts)

    // TODO If performance is an issue, these can be cached until the next call of createSubContext().
    private def conflictingContexts = contexts ++ subContexts

    def createSubContext() = {
      val c = new NameContext(contexts)
      directSubContexts = c :: directSubContexts
      c
    }

    def createUnique(s: String) = {
      val cc = conflictingContexts

      val res = if (!cc.exists(_.identCounters.contains(s))) {
        identCounters.put(s, 0)
        s
      } else {
        val counters = cc.map { c =>
          c.identCounters.get(s) match {
            case None => -1
            case Some(x) => x
          }
        }
        var counter = counters.max + 1
        var newS = s + separator + counter.toString
        while (cc.exists(_.identCounters.contains(newS))) {
          counter += 1
          newS = s + separator + counter.toString
        }
        identCounters.put(s, counter)
        identCounters.put(newS, 0)
        newS
      }

      res
    }

    def createUniqueIdentifier(s: String) = createUnique(createIdentifier(s))

    def createIdentifier(s: String) = DefaultNameGenerator.this.createIdentifier(s)

  }

  def createIdentifier(input: String) = {
    if (input.isEmpty) {
      defaultIdent
    } else {
      val builder = new StringBuilder
      val first = input.head
      if (firstCharacter.findFirstIn(first.toString).isEmpty && !replaceableLetters.contains(first)) {
        builder.append(defaultIdent)
      }
      input foreach {
        c =>
          if (otherCharacter.findFirstIn(c.toString).isDefined) {
            builder.append(c)
          } else if (replaceableLetters.contains(c)) {
            builder.append(replaceableLetters(c))
          }
      }
      var res = builder.result
      while (reservedNames.contains(res)) {
        res = defaultIdent + res
      }
      res
    }
  }

  def createSubContext() = globalContext.createSubContext()

}
