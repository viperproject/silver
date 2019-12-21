// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.decreases

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.Consistency
import viper.silver.verifier.{ConsistencyError, Failure, VerificationResult}

/**
 * Node used to define all possible decreases clauses.
 * Can be used e.g. to filter for decreases clauses.
 */
sealed trait DecreasesExp extends ExtensionExp with Node {

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "DecreasesExp: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("DecreasesExp: verifyExtExp has not been implemented.", pos)))
  }


  /**
    * Condition when the decreases clause should be considered.
    * None means true and is the default.
    */
  val condition: Option[Exp] = None

  /**
   * @return effective condition of the decreases clause
   */
  lazy val getCondition: Exp = condition.getOrElse(TrueLit()(this.pos, NoInfo, NoTrafos))
}

/**
  * Decreases clause defining a tuple as termination measure, potentially with a condition.
  * @param tupleExpressions: expressions defining the termination measure
  * @param condition of the decreases clause
  */
case class DecreasesTuple(tupleExpressions: Seq[Exp] = Nil, override val condition: Option[Exp] = None)
                         (override val pos: Position = NoPosition,
                          override val info: Info = NoInfo,
                          override val errT: ErrorTrafo = NoTrafos) extends DecreasesExp {
  override lazy val extensionIsPure: Boolean = true

  override val typ: Type = Bool

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("decreases") <> space <> ssep(tupleExpressions map (toParenDoc(_)), char(',') <> space)

  override def extensionSubnodes: Seq[Node] = tupleExpressions ++ condition

  /**
   * Allow only pure expressions in the tuple and condition
   */
  override lazy val check: Seq[ConsistencyError] = tupleExpressions.flatMap({
    case _: AccessPredicate => Nil
    case exp: ExtensionExp => Consistency.checkPure(exp)
    case _ => Nil
  }) ++ condition.toSeq.flatMap(Consistency.checkPure)
}

/**
  * Decreases clause defining assumed termination
  * @param condition of the decreases wildcard
  */
case class DecreasesWildcard(override val condition: Option[Exp] = None)
                            (override val pos: Position = NoPosition,
                             override val info: Info = NoInfo,
                             override val errT: ErrorTrafo = NoTrafos) extends DecreasesExp {
  override lazy val extensionIsPure: Boolean = true

  override val typ: Type = Bool

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = text("decreases _")

  override def extensionSubnodes: Seq[Node] = condition.toSeq

  /**
   * Allow only pure expression as condition
   */
  override lazy val check: Seq[ConsistencyError] = condition.toSeq.flatMap(Consistency.checkPure)
}

/**
  * Expression representing the decreases star option (possibly non terminating).
  */
case class DecreasesStar()
                        (override val pos: Position = NoPosition,
                         override val info: Info = NoInfo,
                         override val errT: ErrorTrafo = NoTrafos)
  extends DecreasesExp {
  override val condition: Option[Exp] = None

  override lazy val extensionIsPure: Boolean = true

  override val extensionSubnodes: Seq[Node] = Nil

  override val typ: Type = Bool

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = text("decreases *")
}


/**
 * Container for a possible decreases specification.
 * Can be appended to an AST node as info (metadata).
 * Can contain at most one of each possible decreases clause.
 * @param tuple: optional decreases tuple
 * @param wildcard: optional decreases wildcard
 * @param star: optional decreases star
 */
case class DecreasesContainer(tuple: Option[DecreasesTuple],
                              wildcard: Option[DecreasesWildcard],
                              star: Option[DecreasesStar]) extends Info {

  // The comment of this metadata are the provided decreases clauses
  override def comment: Seq[String] = (tuple ++ wildcard ++ star).map(_.toString()).toSeq
  override def isCached: Boolean = false

  /**
   * Condition for which termination is proven or assumed.
   * I.e. the disjunction of the tuple's and wildcard's condition.
   */
  lazy val terminationCondition: Exp =
    (tuple, wildcard) match {
      case (Some(tuple), Some(wildcard)) =>
        Or(tuple.condition.getOrElse(TrueLit()()), wildcard.condition.getOrElse(TrueLit()()))()
      case (Some(tuple), None) =>
        tuple.condition.getOrElse(TrueLit()())
      case (None, Some(wildcard)) =>
        wildcard.condition.getOrElse(TrueLit()())
      case _ =>
        FalseLit()()
    }

  /**
   * Condition for which the tuple is proven to decrease.
   * The default for a tuple (without condition) is true.
   * If no tuple is given false.
   */
  lazy val tupleCondition: Exp = {
    tuple match {
      case Some(DecreasesTuple(_, Some(condition))) => condition
      case Some(DecreasesTuple(_, None)) => TrueLit()()
      case None => FalseLit()()
    }
  }

  /**
   * @param f: The function, this (Info) should be appended to.
   * @return copy of f with this (Info) appended to,
   */
  def appendToFunction(f: Function): Function = {
    val newInfo = MakeInfoPair(this, f.info)
    f.copy()(f.pos, newInfo, f.errT)
  }

  /**
   * @param m: The method, this (Info) should be appended to.
   * @return copy of m with this (Info) appended to,
   */
  def appendToMethod(m: Method): Method = {
    val newInfo = MakeInfoPair(this, m.info)
    m.copy()(m.pos, newInfo, m.errT)
  }

  /**
   * @param w: The while, this (Info) should be appended to.
   * @return copy of w with this (Info) appended to,
   */
  def appendToWhile(w: While): While = {
    val newInfo = MakeInfoPair(this, w.info)
    w.copy()(w.pos, newInfo, w.errT)
  }
}

object DecreasesContainer {
  /**
   * @return an empty DecreasesContainer.
   */
  def apply(): DecreasesContainer = DecreasesContainer(None, None, None)

  /**
   * @param n: Node possibly containing a DecreasesClause in its metadata (Info).
   * @return DecreasesContainer attached to n (if exists), otherwise, an empty DecreasesContainer.
   */
  def fromNode(n: Node): DecreasesContainer = {
    (n match {
      case ni: Infoed => ni.info.getUniqueInfo[DecreasesContainer]
      case _ => None
    }).getOrElse(DecreasesContainer())
  }
}