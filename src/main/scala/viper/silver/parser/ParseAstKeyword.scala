// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.parser

import viper.silver.ast.utility.lsp.BuiltinFeature
import viper.silver.ast.{NoPosition, Position}
import viper.silver.parser.TypeHelper._

trait PReservedString extends PReservedStringLsp {
  def token: String
  def documentation: BuiltinFeature
  def display: String = token
  def leftPad: String = ""
  def rightPad: String = ""
}
trait LeftSpace extends PReservedString { override def leftPad = " " }
trait RightSpace extends PReservedString { override def rightPad = " " }
case class PReserved[+T <: PReservedString](rs: T)(val pos: (Position, Position)) extends PNode with PLeaf with PReservedLsp[T] {
  override def display = s"${rs.leftPad}${rs.display}${rs.rightPad}"
}
object PReserved {
  def implied[T <: PReservedString](rs: T): PReserved[T] = PReserved(rs)(NoPosition, NoPosition)
}

case class PGrouped[G <: PSym.Group, +T](l: PReserved[G#L], inner: T, r: PReserved[G#R])(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  def update[U](replacement: U): PGrouped[G, U] = PGrouped(l, replacement, r)(pos)
  def update[U, V, D](replacement: Seq[U])(implicit ev: T <:< PDelimited[_, D]) = PGrouped[G, PDelimited[U, D]](l, inner.update(replacement), r)(pos)
  def prettyLines(implicit ev: T <:< PDelimited[_, _]): String = {
    val iPretty = if (inner.length == 0) "" else s"\n  ${inner.prettyLines.replace("\n", "\n  ")}\n"
    s"${l.pretty}${iPretty}${r.pretty}"
  }
}
case object PGrouped {
  def implied[G <: PSym.Group, T](l: G#L, inner: T, r: G#R): PGrouped[G, T] =
    PGrouped[G, T](PReserved.implied(l), inner, PReserved.implied(r))(NoPosition, NoPosition)
  def impliedBracket[T](inner: T): PGrouped[PSym.Bracket, T] = implied[PSym.Bracket, T](PSym.LBracket, inner, PSym.RBracket)
}

case class PDelimited[+T, +D](
  first: Option[T],
  inner: Seq[(D, T)],
  end: Option[D]
)(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  def headOption: Option[T] = first
  def head: T = first.get
  def toSeq: Seq[T] = first.map(_ +: inner.map(_._2)).getOrElse(Nil)
  def delimiters: Seq[D] = inner.map(_._1) ++ end.toSeq
  def length: Int = first.map(_ => 1 + inner.length).getOrElse(0)
  // def toNodes = first.toSeq ++ inner.flatMap(i => Seq(i._1, i._2)) ++ end.toSeq

  def update[U](replacement: Seq[U]): PDelimited[U, D] = {
    assert((first.isEmpty && replacement.isEmpty) || (first.isDefined && inner.length == replacement.length - 1))
    if (replacement.isEmpty) PDelimited(None, Nil, end)(pos)
    else PDelimited(Some(replacement.head), inner.zip(replacement.tail).map { case ((d, _), r) => (d, r) }, end)(pos)
  }
  def prettyLines: String = {
    this.update(this.toSeq.zipWithIndex.map {
      case (e, i) => (if (i == 0) () else PReserved.implied(PSym.Newline), e)
    }).pretty
  }
}

object PDelimited {
  /** Grouped and delimited. */
  type Block[+T <: PNode] = PGrouped[PSym.Brace, PDelimited[T, Option[PSym.Semi]]]

  /** Grouped and comma delimited. */
  type Comma[G <: PSym.Group, +T <: PNode] = PGrouped[G, PDelimited[T, PSym.Comma]]

  def apply[T, D](all: Seq[(T, D)])(pos: (Position, Position)): PDelimited[T, D] = {
    val (ts, ds) = all.unzip
    new PDelimited[T, D](ts.headOption, ds.dropRight(1).zip(ts.drop(1)), ds.lastOption)(pos)
  }
  def empty[T, D]: PDelimited[T, D] = PDelimited(None, Nil, None)(NoPosition, NoPosition)
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
  type Import = PReserved[Import.type]
  case object Define extends PKw("define", BuiltinFeature.Macro) with PKeywordLang
  type Define = PReserved[Define.type]
  case object Field extends PKw("field", BuiltinFeature.Field) with PKeywordLang
  type Field = PReserved[Field.type]
  case object Method extends PKw("method", BuiltinFeature.Method) with PKeywordLang
  type Method = PReserved[Method.type]
  // case class Function(val documentation: BuiltinFeature) extends PKw("function", documentation) with PKeywordLang
  case object Function extends PKw("function", BuiltinFeature.TODO) with PKeywordLang
  type Function = PReserved[Function.type]
  case object Predicate extends PKw("predicate", BuiltinFeature.Predicate) with PKeywordLang
  type Predicate = PReserved[Predicate.type]
  case object Domain extends PKw("domain", BuiltinFeature.Domain) with PKeywordLang
  type Domain = PReserved[Domain.type]
  case object Interpretation extends PKw("interpretation", BuiltinFeature.TODO) with PKeywordLang
  type Interpretation = PReserved[Interpretation.type]
  case object Axiom extends PKw("axiom", BuiltinFeature.TODO) with PKeywordLang
  type Axiom = PReserved[Axiom.type]

  case object Returns extends PKw("returns", BuiltinFeature.TODO) with PKeywordLang
  type Returns = PReserved[Returns.type]
  case object Unique extends PKw("unique", BuiltinFeature.TODO) with PKeywordLang
  type Unique = PReserved[Unique.type]

  sealed trait Spec extends PReservedString; trait AnySpec extends PreSpec with PostSpec with InvSpec
  trait PreSpec extends Spec; trait PostSpec extends Spec; trait InvSpec extends Spec
  case object Requires extends PKw("requires", BuiltinFeature.TODO) with PKeywordLang with PreSpec
  type Requires = PReserved[Requires.type]
  case object Ensures extends PKw("ensures", BuiltinFeature.TODO) with PKeywordLang with PostSpec
  type Ensures = PReserved[Ensures.type]
  case object Invariant extends PKw("invariant", BuiltinFeature.TODO) with PKeywordLang with InvSpec
  type Invariant = PReserved[Invariant.type]

  case object Result extends PKw("result", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom
  type Result = PReserved[Result.type]
  case object Exists extends PKw("exists", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom
  type Exists = PReserved[Exists.type]
  case object Forall extends PKw("forall", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom
  type Forall = PReserved[Forall.type]
  case object Forperm extends PKw("forperm", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom
  type Forperm = PReserved[Forperm.type]
  case object New extends PKw("new", BuiltinFeature.TODO) with PKeywordLang with PKeywordAtom
  type New = PReserved[New.type]

  case object Lhs extends PKw("lhs", BuiltinFeature.TODO) with PKeywordLang
  type Lhs = PReserved[Lhs.type]

  // Stmts
  case object If extends PKw("if", BuiltinFeature.TODO) with PKeywordIf
  type If = PReserved[If.type]
  case object Elseif extends PKw("elseif", BuiltinFeature.TODO) with PKeywordIf
  type Elseif = PReserved[Elseif.type]
  case object Else extends PKw("else", BuiltinFeature.TODO) with PKeywordStmt
  type Else = PReserved[Else.type]
  case object While extends PKw("while", BuiltinFeature.TODO) with PKeywordStmt
  type While = PReserved[While.type]
  case object Fold extends PKw("fold", BuiltinFeature.TODO) with PKeywordStmt
  type Fold = PReserved[Fold.type]
  case object Unfold extends PKw("unfold", BuiltinFeature.TODO) with PKeywordStmt
  type Unfold = PReserved[Unfold.type]
  case object Inhale extends PKw("inhale", BuiltinFeature.TODO) with PKeywordStmt
  type Inhale = PReserved[Inhale.type]
  case object Exhale extends PKw("exhale", BuiltinFeature.TODO) with PKeywordStmt
  type Exhale = PReserved[Exhale.type]
  case object Package extends PKw("package", BuiltinFeature.TODO) with PKeywordStmt
  type Package = PReserved[Package.type]
  case object Apply extends PKw("apply", BuiltinFeature.TODO) with PKeywordStmt
  type Apply = PReserved[Apply.type]
  case object Assert extends PKw("assert", BuiltinFeature.TODO) with PKeywordStmt
  type Assert = PReserved[Assert.type]
  case object Assume extends PKw("assume", BuiltinFeature.TODO) with PKeywordStmt
  type Assume = PReserved[Assume.type]
  case object Var extends PKw("var", BuiltinFeature.TODO) with PKeywordStmt
  type Var = PReserved[Var.type]
  case object Label extends PKw("label", BuiltinFeature.TODO) with PKeywordStmt
  type Label = PReserved[Label.type]
  case object Goto extends PKw("goto", BuiltinFeature.TODO) with PKeywordStmt
  type Goto = PReserved[Goto.type]
  case object Quasihavoc extends PKw("quasihavoc", BuiltinFeature.TODO) with PKeywordStmt
  type Quasihavoc = PReserved[Quasihavoc.type]
  case object Quasihavocall extends PKw("quasihavocall", BuiltinFeature.TODO) with PKeywordStmt
  type Quasihavocall = PReserved[Quasihavocall.type]

  // Constants
  case object True extends PKw("true", BuiltinFeature.TODO) with PKeywordConstant with PKeywordAtom
  type True = PReserved[True.type]
  case object False extends PKw("false", BuiltinFeature.TODO) with PKeywordConstant with PKeywordAtom
  type False = PReserved[False.type]
  case object Null extends PKw("null", BuiltinFeature.TODO) with PKeywordConstant with PKeywordAtom
  type Null = PReserved[Null.type]

  case object None extends PKw("none", BuiltinFeature.TODO) with PKeywordConstant
  type None = PReserved[None.type]
  case object Wildcard extends PKw("wildcard", BuiltinFeature.TODO) with PKeywordConstant
  type Wildcard = PReserved[Wildcard.type]
  case object Write extends PKw("write", BuiltinFeature.TODO) with PKeywordConstant
  type Write = PReserved[Write.type]
  case object Epsilon extends PKw("epsilon", BuiltinFeature.TODO) with PKeywordConstant
  type Epsilon = PReserved[Epsilon.type]

  // Types
  case object Int extends PKw("Int", BuiltinFeature.TODO) with PKeywordType
  type Int = PReserved[Int.type]
  case object Bool extends PKw("Bool", BuiltinFeature.TODO) with PKeywordType
  type Bool = PReserved[Bool.type]
  case object Perm extends PKw("Perm", BuiltinFeature.TODO) with PKeywordType
  type Perm = PReserved[Perm.type]
  case object Ref extends PKw("Ref", BuiltinFeature.TODO) with PKeywordType
  type Ref = PReserved[Ref.type]

  case object Set extends PKw("Set", BuiltinFeature.TODO) with PKeywordType
  type Set = PReserved[Set.type]
  case object Seq extends PKw("Seq", BuiltinFeature.TODO) with PKeywordType
  type Seq = PReserved[Seq.type]
  case object Map extends PKw("Map", BuiltinFeature.TODO) with PKeywordType
  type Map = PReserved[Map.type]
  case object Multiset extends PKw("Multiset", BuiltinFeature.TODO) with PKeywordType
  type Multiset = PReserved[Multiset.type]
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
  // Unused, only temporarily created when calling `prettyLines`
  case object Newline extends PSym("\n") with PSymbolLang
}

/** Anything that can act as an operator. */
trait POperator extends PReservedString with POperatorLsp {
  def operator: String
  override def token = operator
}

trait PSymbolOp extends PSymbol with POperator {
  override def operator = symbol
}
trait PSignaturesOp extends POperator {
  def signatures: List[PTypeSubstitution]
}
trait PUnaryOp extends POperator with PSignaturesOp
trait PBinaryOp extends POperator with PSignaturesOp with LeftSpace with RightSpace
trait PArithOp extends PBinaryOp {
  override def signatures = List(
    Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm))
}
trait PIntOp extends PBinaryOp {
  override def signatures = List(Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int))
}
trait PCmpOp extends PBinaryOp {
  override def signatures = List(
    Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Bool),
    Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Bool))
}
trait PLogicalOp extends PBinaryOp {
  override def signatures = List(Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Bool))
}
trait PEqOp extends PBinaryOp {
  override def signatures = List(Map(POpApp.pArgS(1) -> POpApp.pArg(0), POpApp.pResS -> Bool))
}
trait PCollectionOp extends PBinaryOp
object PCollectionOp {
  val infVar = PTypeVar("#E")
}

object PSymOp {
  case object Wand    extends PSym("--*") with PSymbolOp with PBinaryOp {
    override def signatures = List(
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> TypeHelper.Wand),
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Bool),
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> TypeHelper.Wand, POpApp.pResS -> TypeHelper.Wand),
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> TypeHelper.Wand, POpApp.pResS -> Bool))
  }
  type Wand = PReserved[Wand.type]

  case object EqEq    extends PSym("==")  with PSymbolOp with PBinaryOp with PEqOp
  type EqEq = PReserved[EqEq.type]
  case object Ne      extends PSym("!=")  with PSymbolOp with PBinaryOp with PEqOp
  case object Le      extends PSym("<=")  with PSymbolOp with PBinaryOp with PCmpOp
  case object Ge      extends PSym(">=")  with PSymbolOp with PBinaryOp with PCmpOp
  case object Lt      extends PSym("<")   with PSymbolOp with PBinaryOp with PCmpOp
  case object Gt      extends PSym(">")   with PSymbolOp with PBinaryOp with PCmpOp
  case object AndAnd  extends PSym("&&")  with PSymbolOp with PBinaryOp with PLogicalOp
  case object OrOr    extends PSym("||")  with PSymbolOp with PBinaryOp with PLogicalOp
  case object Implies extends PSym("==>") with PSymbolOp with PBinaryOp with PLogicalOp
  type Implies = PReserved[Implies.type]
  case object Iff    extends PSym("<==>") with PSymbolOp with PBinaryOp with PLogicalOp
  case object Mul     extends PSym("*")   with PSymbolOp with PBinaryOp {
    override def signatures = List(
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Int, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int))
  }
  case object Div     extends PSym("/")   with PSymbolOp with PBinaryOp {
    override def signatures = List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Int, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int))
  }
  case object ArithDiv extends PSym("\\") with PSymbolOp with PBinaryOp with PIntOp
  case object Mod     extends PSym("%")   with PSymbolOp with PBinaryOp with PIntOp
  case object Plus    extends PSym("+")   with PSymbolOp with PBinaryOp with PArithOp
  case object Minus   extends PSym("-")   with PSymbolOp with PBinaryOp with PArithOp
  case object Append  extends PSym("++")  with PSymbolOp with PBinaryOp with PCollectionOp {
    override def signatures = List(
      Map(POpApp.pArgS(0) -> MakeSeq(PCollectionOp.infVar), POpApp.pArgS(1) -> MakeSeq(PCollectionOp.infVar), POpApp.pResS -> MakeSeq(PCollectionOp.infVar)))
  }

  case object Neg     extends PSym("-")   with PSymbolOp with PUnaryOp {
    override def signatures = List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pResS -> Int),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pResS -> Perm))
  }
  case object Not     extends PSym("!")   with PSymbolOp with PUnaryOp {
    override def signatures = List(Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> Bool))
  }

  case object Assign  extends PSym(":=")  with PSymbolOp with LeftSpace with RightSpace
  type Assign = PReserved[Assign.type]
  case object Dot     extends PSym(".")   with PSymbolOp
  type Dot = PReserved[Dot.type]
  case object DotDot  extends PSym("..")  with PSymbolOp
  type DotDot = PReserved[DotDot.type]
  case object Comma   extends PSym(",")   with PSymbolOp
  type Comma = PReserved[Comma.type]
  case object RParen  extends PSym(")")   with PSymbolOp
  type RParen = PReserved[RParen.type]
  case object LBracket extends PSym("[")  with PSymbolOp
  type LBracket = PReserved[LBracket.type]
  case object RBracket extends PSym("]")  with PSymbolOp
  type RBracket = PReserved[RBracket.type]
  case object Question extends PSym("?")  with PSymbolOp with LeftSpace with RightSpace
  type Question = PReserved[Question.type]
  case object Colon   extends PSym(":")   with PSymbolOp with LeftSpace with RightSpace
  type Colon = PReserved[Colon.type]
  case object Or      extends PSym("|")   with PSymbolOp
  type Or = PReserved[Or.type]
}

trait POperatorKeyword extends PKeyword with PKeywordLsp with POperator

trait PSetToSetOp extends PBinaryOp {
  override def signatures = List(
    Map(POpApp.pArgS(0) -> MakeSet(PCollectionOp.infVar), POpApp.pArgS(1) -> MakeSet(PCollectionOp.infVar), POpApp.pResS -> MakeSet(PCollectionOp.infVar)),
    Map(POpApp.pArgS(0) -> MakeMultiset(PCollectionOp.infVar), POpApp.pArgS(1) -> MakeMultiset(PCollectionOp.infVar), POpApp.pResS -> MakeMultiset(PCollectionOp.infVar))
  )
}
trait PInOp extends PBinaryOp {
  override def signatures = List(
    Map(POpApp.pArgS(1) -> MakeSet(POpApp.pArg(0)), POpApp.pResS -> Bool),
    Map(POpApp.pArgS(1) -> MakeSeq(POpApp.pArg(0)), POpApp.pResS -> Bool),
    Map(POpApp.pArgS(1) -> MakeMultiset(POpApp.pArg(0)), POpApp.pResS -> Int),
    Map(POpApp.pArgS(1) -> MakeMap(POpApp.pArg(0), PCollectionOp.infVar), POpApp.pResS -> Bool))
}
trait PSubsetOp extends PBinaryOp {
  override def signatures = List(
    Map(POpApp.pArgS(0) -> MakeSet(PCollectionOp.infVar), POpApp.pArgS(1) -> MakeSet(PCollectionOp.infVar), POpApp.pResS -> Bool),
    Map(POpApp.pArgS(0) -> MakeMultiset(PCollectionOp.infVar), POpApp.pArgS(1) -> MakeMultiset(PCollectionOp.infVar), POpApp.pResS -> Bool))
}

abstract class PKwOp(val keyword: String) extends POperatorKeyword {
  override def operator = keyword

  // TODO:
  override def documentation = BuiltinFeature.TODO
}
object PKwOp {
  case object In            extends PKwOp("in")           with PBinaryOp with PInOp
  type In = PReserved[In.type]
  case object Union         extends PKwOp("union")        with PBinaryOp with PSetToSetOp
  case object Intersection  extends PKwOp("intersection") with PBinaryOp with PSetToSetOp
  case object Setminus      extends PKwOp("setminus")     with PBinaryOp with PSetToSetOp
  case object Subset        extends PKwOp("subset")       with PBinaryOp with PSubsetOp

  case object Unfolding   extends PKwOp("unfolding")  with PKeywordAtom with RightSpace
  type Unfolding = PReserved[Unfolding.type]
  case object Applying    extends PKwOp("applying")   with PKeywordAtom with RightSpace
  type Applying = PReserved[Applying.type]
  case object Let         extends PKwOp("let")        with PKeywordAtom with RightSpace
  type Let = PReserved[Let.type]

  case object Perm        extends PKwOp("perm")       with PKeywordAtom
  type Perm = PReserved[Perm.type]
  case object Acc         extends PKwOp("acc")        with PKeywordAtom
  type Acc = PReserved[Acc.type]
  case object Old         extends PKwOp("old")        with PKeywordAtom
  type Old = PReserved[Old.type]
  case object Domain      extends PKwOp("domain")     with PKeywordAtom
  type Domain = PReserved[Domain.type]
  case object Range       extends PKwOp("range")      with PKeywordAtom
  type Range = PReserved[Range.type]

  case object Seq         extends PKwOp("Seq")        with PKeywordAtom
  type Seq = PReserved[Seq.type]
  case object Set         extends PKwOp("Set")        with PKeywordAtom
  type Set = PReserved[Set.type]
  case object Multiset    extends PKwOp("Multiset")   with PKeywordAtom
  type Multiset = PReserved[Multiset.type]
  case object Map         extends PKwOp("Map")        with PKeywordAtom
  type Map = PReserved[Map.type]
}
