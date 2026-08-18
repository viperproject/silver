// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silver.plugin.sif

import viper.silver.ast.{ExtensionExp, IntLit, NoPosition, Position}
import viper.silver.parser.{NameAnalyser, PExp, PExtender, PIntLit, PType, PTypeSubstitution, Translator, TypeChecker, TypeHelper}

case class PLowExp(e: PExp)(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PExtender with PExp {
  typ = TypeHelper.Bool

  override def typeSubstitutions = e.typeSubstitutions

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    e.forceSubstitution(ts)
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    t.checkTopTyped(e, None)
    if (expected == TypeHelper.Bool || expected == TypeHelper.Impure)
      None
    else
      Some(Seq(s"Expected type ${expected}, but got Bool."))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(e, None)
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    SIFLowExp(t.exp(e))(t.liftPos(this))
  }
}

case class PLowEventExp()(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PExtender with PExp {
  typ = TypeHelper.Bool

  override def typeSubstitutions = Seq()

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {}

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    if (expected == TypeHelper.Bool || expected == TypeHelper.Impure)
      None
    else
      Some(Seq(s"Expected type ${expected}, but got Bool."))
  }

  override def translateExp(t: Translator): ExtensionExp = {
    SIFLowEventExp()(t.liftPos(this))
  }
}

case class PRelExp(e: PExp, i: PIntLit)(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PExtender with PExp {

  override def typeSubstitutions = e.typeSubstitutions

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    e.forceSubstitution(ts)
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(e, None)
    t.checkTopTyped(i, Some(TypeHelper.Int))
    typ = e.typ
    if (i.i == BigInt.int2bigInt(0) || i.i == BigInt.int2bigInt(1))
      None
    else
      Some(Seq(s"Second argument of rel must be 0 or 1, but is ${i.i}."))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    t.checkTopTyped(e, None)
    t.checkTopTyped(i, Some(TypeHelper.Int))
    typ = e.typ
    if (i.i == BigInt.int2bigInt(0) || i.i == BigInt.int2bigInt(1)) {
      if (expected == e.typ)
        None
      else
        Some(Seq(s"Expected type ${expected}, but got ${e.typ}."))
    } else {
      Some(Seq(s"Second argument of rel must be 0 or 1, but is ${i.i}."))
    }
  }

  override def translateExp(t: Translator): ExtensionExp = {
    SIFRelExp(t.exp(e), t.exp(i).asInstanceOf[IntLit])(t.liftPos(this))
  }
}