// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.parser

import viper.silver.ast.utility.lsp.BuiltinFeature
import viper.silver.ast.{NoPosition, Position}

trait PReservedString extends PReservedStringLsp {
  def token: String
  def documentation: BuiltinFeature
  def display: String = token
}
trait LeftSpace; trait RightSpace
case class PReserved[+T <: PReservedString](rs: T)(val pos: (Position, Position)) extends PNode with PLeaf with PReservedLsp[T] {
  override def display = s"${if (rs.isInstanceOf[LeftSpace]) " " else ""}${rs.display}${if (rs.isInstanceOf[RightSpace]) " " else ""}"
}
object PReserved {
  def implied[T <: PReservedString](rs: T): PReserved[T] = PReserved(rs)(NoPosition, NoPosition)
}

case class PGrouped[G <: PSym.Group, +T](l: PReserved[G#L], inner: T, r: PReserved[G#R])(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  def update(replacement: T): PGrouped[G, T] = PGrouped(l, replacement, r)(pos)
}
case object PGrouped {
  def implied[G <: PSym.Group, T](l: G#L, inner: T, r: G#R): PGrouped[G, T] =
    PGrouped[G, T](PReserved.implied(l), inner, PReserved.implied(r))(NoPosition, NoPosition)
}

case class PDelimited[+T, +D](
  first: Option[T],
  inner: Seq[(D, T)],
  end: Option[D]
)(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  def toSeq: Seq[T] = first.map(_ +: inner.map(_._2)).getOrElse(Nil)
  def delimiters: Seq[D] = inner.map(_._1) ++ end.toSeq
  // def toNodes = first.toSeq ++ inner.flatMap(i => Seq(i._1, i._2)) ++ end.toSeq

  def update(replacement: Seq[T]): PDelimited[T, D] = {
    assert((first.isEmpty && replacement.isEmpty) || (first.isDefined && inner.length == replacement.length - 1))
    if (replacement.isEmpty) PDelimited(None, Nil, end)(pos)
    else PDelimited(Some(replacement.head), inner.zip(replacement.tail).map { case ((d, _), r) => (d, r) }, end)(pos)
  }
}

////
// Keywords
////
/** Anything that is composed of /[a-zA-Z]/ characters. */
trait PKeyword extends PReservedString {
  def keyword: String
  override def token = keyword
}

trait PKeywordLang extends PKeyword with PKeywordLsp
trait PKeywordStmt extends PKeyword with PKeywordStmtLsp
trait PKeywordType extends PKeyword with PKeywordTypeLsp
trait PKeywordConstant extends PKeyword with PKeywordLsp

sealed trait PKeywordAtom
sealed trait PKeywordIf extends PKeywordStmt


abstract class PKw(val keyword: String, val documentation: BuiltinFeature) extends PKeyword
object PKw {
  case object Import extends PKw("import", BuiltinFeature.Import) with PKeywordLang
  case object Define extends PKw("define", BuiltinFeature.Macro) with PKeywordLang
  case object Field extends PKw("field", BuiltinFeature.Field) with PKeywordLang
  case object Method extends PKw("method", BuiltinFeature.Method) with PKeywordLang
  // case class Function(val documentation: BuiltinFeature) extends PKw("function", documentation) with PKeywordLang
  case object Function extends PKw("function", BuiltinFeature.TODO) with PKeywordLang
  case object Predicate extends PKw("predicate", BuiltinFeature.Predicate) with PKeywordLang
  case object Domain extends PKw("domain", BuiltinFeature.Domain) with PKeywordLang
  case object Interpretation extends PKw("interpretation", BuiltinFeature.TODO) with PKeywordLang
  case object Axiom extends PKw("axiom", BuiltinFeature.TODO) with PKeywordLang

  case object Returns extends PKw("returns", BuiltinFeature.TODO) with PKeywordLang
  case object Unique extends PKw("unique", BuiltinFeature.TODO) with PKeywordLang

  sealed trait Spec extends PReservedString; trait PreSpec extends Spec; trait PostSpec extends Spec; trait InvSpec extends Spec
  case object Requires extends PKw("requires", BuiltinFeature.TODO) with PKeywordLang with PreSpec
  case object Ensures extends PKw("ensures", BuiltinFeature.TODO) with PKeywordLang with PostSpec
  case object Invariant extends PKw("invariant", BuiltinFeature.TODO) with PKeywordLang with InvSpec

  case object Result extends PKw("result", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom
  case object Exists extends PKw("exists", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom
  case object Forall extends PKw("forall", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom
  case object Forperm extends PKw("forperm", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom
  case object New extends PKw("new", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom

  case object Lhs extends PKw("lhs", BuiltinFeature.TODO) with PKeywordLang

  // Stmts
  case object If extends PKw("if", BuiltinFeature.TODO) with PKeywordIf
  case object Elseif extends PKw("elseif", BuiltinFeature.TODO) with PKeywordIf
  case object Else extends PKw("else", BuiltinFeature.TODO) with PKeywordStmt
  case object While extends PKw("while", BuiltinFeature.TODO) with PKeywordStmt
  case object Fold extends PKw("fold", BuiltinFeature.TODO) with PKeywordStmt
  case object Unfold extends PKw("unfold", BuiltinFeature.TODO) with PKeywordStmt
  case object Inhale extends PKw("inhale", BuiltinFeature.TODO) with PKeywordStmt
  case object Exhale extends PKw("exhale", BuiltinFeature.TODO) with PKeywordStmt
  case object Package extends PKw("package", BuiltinFeature.TODO) with PKeywordStmt
  case object Apply extends PKw("apply", BuiltinFeature.TODO) with PKeywordStmt
  case object Assert extends PKw("assert", BuiltinFeature.TODO) with PKeywordStmt
  case object Assume extends PKw("assume", BuiltinFeature.TODO) with PKeywordStmt
  case object Var extends PKw("var", BuiltinFeature.TODO) with PKeywordStmt
  case object Label extends PKw("label", BuiltinFeature.TODO) with PKeywordStmt
  case object Goto extends PKw("goto", BuiltinFeature.TODO) with PKeywordStmt
  case object Quasihavoc extends PKw("quasihavoc", BuiltinFeature.TODO) with PKeywordStmt
  case object Quasihavocall extends PKw("quasihavocall", BuiltinFeature.TODO) with PKeywordStmt

  // Constants
  case object True extends PKw("true", BuiltinFeature.TODO) with PKeywordConstant with PKeywordAtom
  case object False extends PKw("false", BuiltinFeature.TODO) with PKeywordConstant with PKeywordAtom
  case object Null extends PKw("null", BuiltinFeature.TODO) with PKeywordConstant with PKeywordAtom

  case object None extends PKw("none", BuiltinFeature.TODO) with PKeywordConstant
  case object Wildcard extends PKw("wildcard", BuiltinFeature.TODO) with PKeywordConstant
  case object Write extends PKw("write", BuiltinFeature.TODO) with PKeywordConstant
  case object Epsilon extends PKw("epsilon", BuiltinFeature.TODO) with PKeywordConstant

  // Types
  case object Int extends PKw("Int", BuiltinFeature.TODO) with PKeywordType
  case object Bool extends PKw("Bool", BuiltinFeature.TODO) with PKeywordType
  case object Perm extends PKw("Perm", BuiltinFeature.TODO) with PKeywordType
  case object Ref extends PKw("Ref", BuiltinFeature.TODO) with PKeywordType

  case object Set extends PKw("Set", BuiltinFeature.TODO) with PKeywordType
  case object Seq extends PKw("Seq", BuiltinFeature.TODO) with PKeywordType
  case object Map extends PKw("Map", BuiltinFeature.TODO) with PKeywordType
  case object Multiset extends PKw("Multiset", BuiltinFeature.TODO) with PKeywordType
}

/** Anything that is composed of /![a-zA-Z]/ characters. */
trait PSymbol extends PReservedString {
  def symbol: String
  override def token = symbol

  // TODO:
  override def documentation = BuiltinFeature.TODO
}

trait PSymbolLang extends PSymbol with PSymbolLangLsp

abstract class PSym(val symbol: String) extends PSymbol
object PSym {
  sealed trait Group extends PSymbol {
    type L <: Group; type R <: Group
  }
  sealed trait Paren extends Group {
    type L = LParen.type; type R = RParen.type
  }
  case object LParen extends PSym("(") with PSymbolLang with Paren
  type LParen = PReserved[LParen.type]
  case object RParen extends PSym(")") with PSymbolLang with Paren
  type RParen = PReserved[RParen.type]
  sealed trait Angle extends Group {
    type L = LAngle.type; type R = RAngle.type
  }
  case object LAngle extends PSym("<") with PSymbolLang with Angle
  type LAngle = PReserved[LAngle.type]
  case object RAngle extends PSym(">") with PSymbolLang with Angle
  type RAngle = PReserved[RAngle.type]
  sealed trait Brace extends Group {
    type L = LBrace.type; type R = RBrace.type
  }
  case object LBrace extends PSym("{") with PSymbolLang with Brace
  type LBrace = PReserved[LBrace.type]
  case object RBrace extends PSym("}") with PSymbolLang with Brace
  type RBrace = PReserved[RBrace.type]
  sealed trait Bracket extends Group {
    type L = LBracket.type; type R = RBracket.type
  }
  case object LBracket extends PSym("[") with PSymbolLang with Bracket
  type LBracket = PReserved[LBracket.type]
  case object RBracket extends PSym("]") with PSymbolLang with Bracket
  type RBracket = PReserved[RBracket.type]
  case object Quote extends PSym("\"") with PSymbolLang with Group {
    type L = Quote.type; type R = Quote.type
  }
  type Quote = PReserved[Quote.type]

  case object Comma extends PSym(",") with PSymbolLang with RightSpace {
    override def display = ", "
  }
  type Comma = PReserved[Comma.type]
  case object Semi extends PSym(";") with PSymbolLang
  type Semi = PReserved[Semi.type]

  // Used for domain interpretations or type annotations
  case object Colon extends PSym(":") with PSymbolLang with RightSpace
  type Colon = PReserved[Colon.type]
  // Used for quantifiers
  case object ColonColon extends PSym("::") with PSymbolLang with LeftSpace with RightSpace
  type ColonColon = PReserved[ColonColon.type]
  // Used for annotations
  case object At extends PSym("@") with PSymbolLang
  type At = PReserved[At.type]
  // Used for `new(*)`
  case object Star extends PSym("*") with PSymbolLang
  type Star = PReserved[Star.type]

  /** Grouped and delimited. */
  type Punctuated[G <: Group, T <: PNode] = PGrouped[G, PDelimited[T, Comma]]
}

/** Anything that can act as an operator. */
trait POperator extends PReservedString with POperatorLsp {
  def operator: String
  override def token = operator
}

trait PSymbolOp extends PSymbol with POperator {
  override def operator = symbol
}
trait PBinaryOp extends POperator with LeftSpace with RightSpace
trait PUnaryOp extends POperator

object PSymOp {
  case object Wand extends PSym("--*") with PSymbolOp with PBinaryOp

  case object EqEq extends PSym("==") with PSymbolOp with PBinaryOp
  case object Ne extends PSym("!=") with PSymbolOp with PBinaryOp
  case object Le extends PSym("<=") with PSymbolOp with PBinaryOp
  case object Ge extends PSym(">=") with PSymbolOp with PBinaryOp
  case object Lt extends PSym("<") with PSymbolOp with PBinaryOp
  case object Gt extends PSym(">") with PSymbolOp with PBinaryOp
  case object AndAnd extends PSym("&&") with PSymbolOp with PBinaryOp
  case object OrOr extends PSym("||") with PSymbolOp with PBinaryOp
  case object Implies extends PSym("==>") with PSymbolOp with PBinaryOp
  case object Iff extends PSym("<==>") with PSymbolOp with PBinaryOp
  case object Mul extends PSym("*") with PSymbolOp with PBinaryOp
  case object Div extends PSym("/") with PSymbolOp with PBinaryOp
  case object ArithDiv extends PSym("\\") with PSymbolOp with PBinaryOp
  case object Mod extends PSym("%") with PSymbolOp with PBinaryOp
  case object Plus extends PSym("+") with PSymbolOp with PBinaryOp
  case object Minus extends PSym("-") with PSymbolOp with PBinaryOp
  case object Neg extends PSym("-") with PSymbolOp with PUnaryOp
  case object Not extends PSym("!") with PSymbolOp with PUnaryOp

  case object Append extends PSym("++") with PSymbolOp with PBinaryOp

  case object Assign extends PSym(":=") with PSymbolOp with LeftSpace with RightSpace
  type Assign = PReserved[Assign.type]
  case object Dot extends PSym(".") with PSymbolOp
  case object DotDot extends PSym("..") with PSymbolOp
  case object Comma extends PSym(",") with PSymbolOp
  case object RParen extends PSym(")") with PSymbolOp
  case object LBracket extends PSym("[") with PSymbolOp
  case object RBracket extends PSym("]") with PSymbolOp
  case object Question extends PSym("?") with PSymbolOp with LeftSpace with RightSpace
  case object Colon extends PSym(":") with PSymbolOp with LeftSpace with RightSpace
  case object Or extends PSym("|") with PSymbolOp
}

trait POperatorKeyword extends PKeyword with PKeywordLsp with POperator

abstract class PKwOp(val keyword: String) extends POperatorKeyword {
  override def operator = keyword

  // TODO:
  override def documentation = BuiltinFeature.TODO
}
object PKwOp {
  case object In extends PKwOp("in") with PBinaryOp
  case object Union extends PKwOp("union") with PBinaryOp
  case object Intersection extends PKwOp("intersection") with PBinaryOp
  case object Setminus extends PKwOp("setminus") with PBinaryOp
  case object Subset extends PKwOp("subset") with PBinaryOp

  case object Unfolding extends PKwOp("unfolding") with PKeywordAtom with RightSpace
  case object Applying extends PKwOp("applying") with PKeywordAtom with RightSpace
  case object Let extends PKwOp("let") with PKeywordAtom with RightSpace

  case object Perm extends PKwOp("perm") with PKeywordAtom
  case object Acc extends PKwOp("acc") with PKeywordAtom
  case object Old extends PKwOp("old") with PKeywordAtom
  case object Domain extends PKwOp("domain") with PKeywordAtom
  case object Range extends PKwOp("range") with PKeywordAtom

  case object Seq extends PKwOp("Seq") with PKeywordAtom
  case object Set extends PKwOp("Set") with PKeywordAtom
  case object Multiset extends PKwOp("Multiset") with PKeywordAtom
  case object Map extends PKwOp("Map") with PKeywordAtom
}



// /** Keywords such a `union`, `in`, `intersect`, `acc`, `new`, `perm`, etc. */
// case class PKeywordOperator(keyword: String)(val pos: (Position, Position)) extends PKeyword with PKeywordLsp with POperator {
//   override def operator = keyword
// }
// /** Operators such a `--*`, `==`, `<=`, `-`, etc. */
// case class POperatorSymbol(operator: String)(val pos: (Position, Position)) extends POperator with POperatorLsp

