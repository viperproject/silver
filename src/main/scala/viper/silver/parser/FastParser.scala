package viper.silver.parser

/**
  * Created by sahil on 24.05.16.
  */

import java.nio.file.Path

import fastparse.Implicits.{Repeater, Sequencer}
import fastparse.parsers.Combinators.{Repeat, Rule, Sequence}
import fastparse.{Implicits, WhitespaceApi}
import fastparse.all._
import fastparse.core.Mutable.{Failure, Success}
import fastparse.core.Parsed.Failure.Extra
import fastparse.core.Parsed.{Position, TracedFailure}
import fastparse.parsers.Intrinsics
import fastparse.core.{Mutable, ParseCtx, Parsed, Parser}
import fastparse.parsers.Terminals.Pass
import fastparse.parsers.{Intrinsics, Terminals}
import viper.silver.ast.{HasLineColumn, SourcePosition}
import viper.silver.FastPositions

import scala.annotation.tailrec
import scala.reflect.internal.util.Position
/*import fastparse.core.{Parsed, Parser}*/
import fastparse.parsers.Intrinsics
import viper.silver.verifier.{ParseError, ParseReport, ParseWarning}

import scala.collection.immutable.Iterable
import scala.collection.mutable
import scala.language.implicitConversions
import scala.language.reflectiveCalls

case class PFilePosition(file: Path, vline: Int , col: Int) extends util.parsing.input.Position with HasLineColumn
{
  override lazy val line = vline
  override lazy val column = col
  override lazy val lineContents = toString
  override lazy val toString = s"${file.getFileName}@$vline.$col"
  //  println(toString)
}

class PosRepeat[T, +R](p: Parser[T], min: Int, max: Int, delimiter: Parser[_],file: Path)
                        (implicit ev: Implicits.Repeater[T, R]) extends Repeat[T, R](p, min, max, delimiter){

  def computeFrom(input: String, index: Int) : (Int, Int) = {
    val lines = input.take(1 + index).lines.toVector
    val line = lines.length
    val col = lines.lastOption.map(_.length).getOrElse(0)
    (line, col)
  }

 override def parseRec(cfg: ParseCtx, index: Int) = {
    @tailrec def rec(index: Int,
                     del: Parser[_],
                     lastFailure: Mutable.Failure,
                     acc: ev.Acc,
                     cut: Boolean,
                     count: Int): Mutable[R] = {
      del.parseRec(cfg, index) match{
        case f1: Mutable.Failure =>
          val cut1 = f1.cut
          if (cut1) failMore(f1, index, cfg.logDepth, cut = true)
          else passInRange(cut, f1, index, ev.result(acc), count)

        case Mutable.Success(value0, index0, traceParsers0, cut0)  =>
          p.parseRec(cfg, index0) match{
            case f2: Mutable.Failure =>
              val cut2 = f2.cut
              if (cut2 | cut0) failMore(f2, index0, cfg.logDepth, cut = true)
              else passInRange(cut | cut0, f2, index, ev.result(acc), count)

            case Mutable.Success(value1, index1, traceParsers1, cut1)  =>
              ev.accumulate(value1, acc)
              val counted = count + 1
              val start1 = computeFrom(cfg.input, index0)
              val end1 = computeFrom(cfg.input, index1)
              viper.silver.FastPositions.setStart(value1, PFilePosition(file, start1._1, start1._2))
              viper.silver.FastPositions.setFinish (value1, PFilePosition(file, end1._1, end1._2))
              if (counted < max)
                rec(index1, delimiter, lastFailure, acc, cut0 | cut1, counted)
              else
                passInRange(cut0 | cut1, lastFailure, index1, ev.result(acc), counted)
          }
      }
    }

    def passInRange(cut: Boolean,
                    lastFailure: Mutable.Failure,
                    finalIndex: Int,
                    acc: R,
                    count: Int) = {
      if (min <= count) {
        val parsers =
          if (null == lastFailure) Set.empty[Parser[_]]
          else lastFailure.traceParsers
        success(cfg.success, acc, finalIndex, parsers, cut)
      } else failMore(lastFailure, index, cfg.logDepth, cut = cut)
    }

    // don't call the parseRec at all, if max is "0", as our parser corresponds to `Pass` in that case.
    if (max == 0 ) {
      success(cfg.success, ev.result(ev.initial), index, Set.empty[Parser[_]], false)
    } else {
      rec(index, Pass, null, ev.initial, false, 0)
    }
  }
  override def toString = {
    val things = Seq(
      if (min == 0) None else Some(min),
      if (delimiter == Pass) None else Some("sep = " + delimiter),
      if (max == Int.MaxValue) None else Some("max = " + max)
    ).flatten.mkString(", ")
    if (things.isEmpty) opWrap(p) + ".rep"
    else s"${opWrap(p)}.rep($things)"
  }
}

class PosCustomSequence[+T, +R, +V](WL: P0, p0: P[T], p: P[V], cut: Boolean, file: Path)
                                   (implicit ev: Sequencer[T, V, R]) extends WhitespaceApi.CustomSequence(WL, p0, p, cut)(ev){

  def computeFrom(input: String, index: Int) : (Int, Int) = {
    val lines = input.take(1 + index).lines.toVector
    val line = lines.length
    val col = lines.lastOption.map(_.length).getOrElse(0)
    (line, col)
  }

  override def parseRec(cfg: ParseCtx, index: Int) = {
    p0.parseRec(cfg, index) match {
      case f: Mutable.Failure => failMore(f, index, cfg.logDepth, f.traceParsers, false)
      case Mutable.Success(value0, index0, traceParsers0, cut0) =>
        val start0 = computeFrom(cfg.input, index)
        val end0 = computeFrom(cfg.input, index0)
        viper.silver.FastPositions.setStart (value0, PFilePosition(file, start0._1, start0._2))
        viper.silver.FastPositions.setFinish (value0, PFilePosition(file, end0._1, end0._2))
        WL.parseRec(cfg, index0) match {
          case f1: Mutable.Failure => failMore(f1, index, cfg.logDepth)
          case Mutable.Success(value1, index1, traceParsers1, cut1) =>
            p.parseRec(cfg, index1) match {
              case f: Mutable.Failure => failMore(
                f, index1, cfg.logDepth,
                mergeTrace(cfg.traceIndex, traceParsers0, f.traceParsers),
                cut | cut0
              )
              case Mutable.Success(value2, index2, traceParsers2, cut2) =>
                val start1 = computeFrom(cfg.input, index1)
                val end1 = computeFrom(cfg.input, index2)
                viper.silver.FastPositions.setStart (value2, PFilePosition(file, start1._1, start1._2))
                viper.silver.FastPositions.setFinish (value2, PFilePosition(file, end1._1, end1._2))
                val (newIndex, newCut) =
                  if (index2 > index1 || index1 == cfg.input.length) (index2, cut | cut0 | cut1 | cut2)
                  else (index0, cut | cut0 | cut2)

                success(
                  cfg.success,
                  ev.apply(value0, value2),
                  newIndex,
                  mergeTrace(cfg.traceIndex, traceParsers0, traceParsers2),
                  newCut
                )
            }
        }
    }
  }

}


class PositionRule[+T](override val name: String, override val p: () => Parser[T], file: Path) extends Rule[T](name, p){
  lazy val pCached = p()

  override def parseRec(cfg: ParseCtx, index: Int) = {


    def computeFrom(input: String, index: Int) : (Int, Int) = {
      val lines = input.take(1 + index).lines.toVector
      val line = lines.length
      val col = lines.lastOption.map(_.length).getOrElse(0)
      (line, col)
    }
    if (cfg.instrument == null) {
      pCached.parseRec(cfg, index) match{
        case f: Mutable.Failure => failMore(f, index, cfg.logDepth)
        case s: Mutable.Success[T] =>
          val start = computeFrom(cfg.input, index)
          val end = computeFrom(cfg.input, s.index)
          viper.silver.FastPositions.setStart (s.value, PFilePosition(file, start._1, start._2))
          viper.silver.FastPositions.setFinish (s.value, PFilePosition(file, end._1, end._2))
          //          println(file)

          s
      }
    } else {
      lazy val res = pCached.parseRec(cfg, index) match{
        case f: Mutable.Failure => failMore(f, index, cfg.logDepth)
        case s: Mutable.Success[T] => {
          val start = computeFrom(cfg.input, index)
          val end = computeFrom(cfg.input, s.index)
          viper.silver.FastPositions.setStart (s.value, PFilePosition(file, start._1, start._2))
          viper.silver.FastPositions.setFinish (s.value, PFilePosition(file, end._1, end._2))

          s
        }
      }
      cfg.instrument(this, index, () => res.toResult)
      res
    }
  }
}




case class argException(pos: scala.util.parsing.input.Position)  extends Exception



object FastParser {

  var _file: Path = null
  var _imports: mutable.HashMap[Path, Boolean] = null

  def parse(s: String, f: Path) = {
    _file = f
      _imports = mutable.HashMap((f, true))
    try {
      val rp = RecParser(f).parses(s)
      rp match {
        case _ => rp
        //      case rp.Error(a, b) => Error(a, b)
      }
    }
    catch {
      case e@argException(pos) => new ParseError("Arg Number does not match" , SourcePosition(_file, pos.line,pos.column))


    }


  }

  case class RecParser(file: Path) {
    def parses(s: String) = fastparser.parse(s)
  }

  def P[T](p: => Parser[T])(implicit name: sourcecode.Name): Parser[T] =
    new PositionRule(name.value, () => p, _file)

  def PWrapper(WL: P0) = new PWrapper(WL)
  class PWhitespaceApi[V](p0: P[V], WL: P0) extends WhitespaceApi[V](p0, WL){
    //        override def ~[V, R](p: P[V])
    //                            (implicit ev: Sequencer[T, V, R])
    //        : P[R] = {
    //          assert(p != null)
    //          new WhitespaceApi.CustomSequence(WL, if (p0 != WL) p0 else Pass.asInstanceOf[P[T]], p, cut=false)(ev)
    //        }


    override def repX[R](implicit ev: Repeater[V, R]): Parser[R] = new PosRepeat(p0, 0, Int.MaxValue, Pass, _file)

    override def rep[R](implicit ev: Repeater[V, R]): Parser[R] = new PosRepeat(p0, 0, Int.MaxValue, NoCut(WL), _file)

    override def repX[R](min: Int = 0, sep: Parser[_] = Pass, max: Int = Int.MaxValue)
               (implicit ev: Repeater[V, R]): Parser[R] =  new PosRepeat(p0, min, max, sep, _file)

    override def rep[R](min: Int = 0, sep: Parser[_] = Pass, max: Int = Int.MaxValue)
                       (implicit ev: Repeater[V, R]): Parser[R] = {
      new PosRepeat(p0, min, max, if (sep != Pass) NoCut(WL) ~ sep ~ NoCut(WL) else NoCut(WL), _file)
    }
//    override def rep[R](min: Int = 0, sep: P[_] = Pass, max: Int = Int.MaxValue)
//               (implicit ev: Repeater[V, R]): P[R] = {
//      Repeat(p0, min, max, if (sep != Pass) NoCut(WL) ~ sep ~ NoCut(WL) else NoCut(WL))
//    }


    override def ~[V2, R](p: Parser[V2])(implicit ev: Sequencer[V, V2, R]): Parser[R] = {
      assert(p != null)
      new PosCustomSequence[V, R, V2](WL, if (p0 != WL) p0 else Pass.asInstanceOf[P[V]], p, cut=false, _file)(ev)
    }



    override def ~/[V2, R](p: P[V2])
                          (implicit ev: Sequencer[V, V2, R])
    : P[R] = {
      assert(p != null)
      new PosCustomSequence(WL, if (p0 != WL) p0 else Pass.asInstanceOf[P[V]], p, cut=true, _file)(ev)
    }
  }
  class PWrapper(WL: P0){
    implicit def parserApi[T, V](p0: T)(implicit c: T => P[V]): PWhitespaceApi[V] =

      new PWhitespaceApi[V](p0, WL)
  }

  val White = PWrapper {
    import fastparse.all._

    NoTrace((("/*" ~ (AnyChar ~ !StringIn("*/")).rep ~ AnyChar ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ "\n") | " " | "\t" | "\n" | "\r").rep)
  }

  import fastparse.noApi._

  //     import fastparse.all._
  import White._


  // code starts from here

  def tester(test: String) = "1"

  //from here the code starts
  def keyword(check: String) = check ~~ !CharIn('0' to '9', 'A' to 'Z', 'a' to 'z', "$_")

  def parens[A](p: fastparse.noApi.Parser[A]) = "(" ~ p ~ ")"

  def quoted[A](p:fastparse.noApi.Parser[A]) = "\"" ~ p ~ "\""

  def foldPExp[E <: PExp](e: PExp, es: Seq[PExp => E]): E =
    es.foldLeft(e) { (t, a) =>
      val result = a(t)
      result.setPos(t)
      result
    }.asInstanceOf[E]

  def getFieldAccess(obj: Any) = obj match {
    case n: PFieldAccess => true
    case _ => false
  }

  def expandDefines(defines: Seq[PDefine], toExpand: Seq[PDefine]): Seq[PDefine] = {
    val maxCount = 25
    /* TODO: Totally arbitrary cycle breaker. We should properly detect
     * (mutually) recursive named assertions.
     */
    var count = 0
    var definesToExpand = toExpand
    var expandedIds = Seq[String]()

    do {
      expandedIds = Seq.empty
      count += 1

      definesToExpand = definesToExpand.map(define => {
        val optExpandedDefine = doExpandDefines[PDefine](defines, define)
        expandedIds = optExpandedDefine.map(_.idndef.name).toSeq ++ expandedIds

        optExpandedDefine.getOrElse(define)
      })
    } while (expandedIds.nonEmpty && count <= maxCount)

    if (count > maxCount)
      sys.error(s"Couldn't expand all named assertions in $maxCount cycles. "
        + s"Might there be a mutual recursion involving $expandedIds?")

    definesToExpand
  }

  def doExpandDefines[N <: PNode](defines: Seq[PDefine], node: N): Option[N] = {
    var expanded = false

    def lookupOrElse(piu: PIdnUse, els: PNode) =
      defines.find(_.idndef.name == piu.name).fold[PNode](els) _

    def expandAllegedInvocation(target: PIdnUse, targetArgs: Seq[PExp], els: PNode): PNode = {
      /* Potentially expand a named assertion that takes arguments, e.g. A(x, y) */
      lookupOrElse(target, els)(define => define.args match {
        case None =>
          /* There is a named assertion with name `target`, but the named
           * assertion takes arguments. Hence, `target` cannot denote the
           * use of a named assertion.
           */
          els
        case Some(args) if targetArgs.length != args.length =>
          /* Similar to the previous case */
          throw new argException(FastPositions.getStart(target))
//          els
        case Some(args) =>
          expanded = true

          define.body.transform {
            /* Expand the named assertion's formal arguments by the given actual arguments */
            case piu: PIdnUse =>
              args.indexWhere(_.name == piu.name) match {
                case -1 => piu
                case i => targetArgs(i)
              }
          }() : PNode /* [2014-06-31 Malte] Type-checker wasn't pleased without it */
      })
    }

    val potentiallyExpandedNode =

      node.transform {
        case piu: PIdnUse =>
          /* Potentially expand a named assertion that takes no arguments, e.g. A.
           * If piu (which is a symbol) denotes a named assertion (i.e. if there
           * is a define in defines whose name is piu), then it is replaced by
           * the body of the named assertion.
           */
          lookupOrElse(piu, piu)(define => {
            expanded = true

            define.body
          })



             case fapp: PFunctApp => expandAllegedInvocation(fapp.func, fapp.args, fapp)
             case call: PMethodCall => expandAllegedInvocation(call.method, call.args, call)
      }(recursive = _ => true)

    if (expanded) Some(potentiallyExpandedNode)
    else None
  }

  /** The file we are currently parsing (for creating positions later). */
  def file: Path = null

  def expandDefines[N <: PNode](defines: Seq[PDefine], node: N): N =
    doExpandDefines(defines, node).getOrElse(node)


  //iskey gives if given string is a key or not

  val iskey = P(StringIn(// special variables
    "result",
    // types
    "Int", "Perm", "Bool", "Ref", "Rational",
    // boolean constants
    "true", "false",
    // null
    "null",
    // preamble importing
    "import",
    // declaration keywords
    "method", "function", "predicate", "program", "domain", "axiom", "var", "returns", "field", "define", "wand",
    // specifications
    "requires", "ensures", "invariant",
    // statements
    "fold", "unfold", "inhale", "exhale", "new", "assert", "assume", "package", "apply",
    // control flow
    "while", "if", "elseif", "else", "goto", "label",
    // special fresh block
    "fresh", "constraining",
    // sequences
    "Seq",
    // sets and multisets
    "Set", "Multiset", "union", "intersection", "setminus", "subset",
    // prover hint expressions
    "unfolding", "in", "folding", "applying", "packaging",
    // old expression
    "old", "lhs",
    // other expressions
    "let",
    // quantification
    "forall", "exists", "forperm",
    // permission syntax
    "acc", "wildcard", "write", "none", "epsilon", "perm",
    // modifiers
    "unique") ~~ !CharIn('0' to '9', 'A' to 'Z', 'a' to 'z'))

  val keywords = Set("result",
    // types
    "Int", "Perm", "Bool", "Ref", "Rational",
    // boolean constants
    "true", "false",
    // null
    "null",
    // preamble importing
    "import",
    // declaration keywords
    "method", "function", "predicate", "program", "domain", "axiom", "var", "returns", "field", "define", "wand",
    // specifications
    "requires", "ensures", "invariant",
    // statements
    "fold", "unfold", "inhale", "exhale", "new", "assert", "assume", "package", "apply",
    // control flow
    "while", "if", "elseif", "else", "goto", "label",
    // special fresh block
    "fresh", "constraining",
    // sequences
    "Seq",
    // sets and multisets
    "Set", "Multiset", "union", "intersection", "setminus", "subset",
    // prover hint expressions
    "unfolding", "in", "folding", "applying", "packaging",
    // old expression
    "old", "lhs",
    // other expressions
    "let",
    // quantification
    "forall", "exists", "forperm",
    // permission syntax
    "acc", "wildcard", "write", "none", "epsilon", "perm",
    // modifiers
    "unique")


  lazy val atom: P[PExp] = P(integer | booltrue | boolfalse | nul | old | applyOld
    | keyword("result").map { _ => PResultLit() } | (CharIn("-!+").! ~ sum).map { case (a, b) => PUnExp(a, b) }
    | "(" ~ exp ~ ")" | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | folding | applying
    | packaging | setTypedEmpty | explicitSetNonEmpty | explicitMultisetNonEmpty | multiSetTypedEmpty | seqTypedEmpty
    | seqLength | explicitSeqNonEmpty | seqRange | fapp | typedFapp | idnuse)

//    lazy val atom: P[PExp] = P(seqRange|seqLength| integer|idnuse )

  lazy val integer: P[PIntLit] = P(CharIn('0' to '9').rep(1)).!.map { s => PIntLit(BigInt(s)) }
  lazy val booltrue: P[PBoolLit] = P(keyword("true")).map(_ => PBoolLit(b = true))
  lazy val boolfalse: P[PBoolLit] = P(keyword("false")).map(_ => PBoolLit(b = false))
  lazy val nul: P[PNullLit] = P(keyword("null")).map(_ => PNullLit())

  lazy val identifier: P[Unit] = P(CharIn('A' to 'Z', 'a' to 'z', "$_") ~~ CharIn('0' to '9', 'A' to 'Z', 'a' to 'z', "$_").repX)
  lazy val ident: P[String] = P(identifier.!).filter{case a => !keywords.contains(a)}
  //possible customize error code in rule ident
  lazy val idnuse: P[PIdnUse] = P(ident).map(PIdnUse)

  lazy val old: P[PExp] = P(StringIn("old") ~ (parens(exp).map(POld) | ("[" ~ idnuse ~ "]" ~ parens(exp)).map { case (a, b) => PLabelledOld(a, b) }))
  lazy val applyOld: P[PExp] = P((StringIn("lhs") ~ parens(exp)).map(PApplyOld))
  lazy val magicWandExp: P[PExp] = P(orExp ~ ("--*".! ~ magicWandExp).?).map{ case(a, b) => b match {
      case Some(c) => PBinExp(a, c._1,c._2 )
      case None => a
    }
  }

  lazy val realMagicWandExp: P[PExp] = P((orExp ~ "--*".! ~ magicWandExp).map { case (a, b, c) => PBinExp(a, b, c) })
  lazy val implExp: P[PExp] = P(magicWandExp ~ (StringIn("==>").! ~ implExp).?).map{ case(a, b) => b match {
      case Some(c) => PBinExp(a, c._1,c._2 )
      case None => a
    }
  }
  lazy val iffExp: P[PExp] = P(implExp ~ ("<==>".! ~ iffExp).?).map{ case(a, b) => b match {
      case Some(c) => PBinExp(a, c._1,c._2 )
      case None => a
    }
  }
//  lazy val iteExpr: P[PExp] = P((iffExp ~ "?" ~ iteExpr ~ ":" ~ iteExpr).map { case (a, b, c) => PCondExp(a, b, c) } | iffExp)
  lazy val iteExpr: P[PExp] = P(iffExp ~ ("?" ~ iteExpr ~ ":" ~ iteExpr).?).map{ case(a, b) => b match {
      case Some(c) => PCondExp(a, c._1,c._2 )
      case None => a
    }
  }
  lazy val exp: P[PExp] = P(iteExpr)

  lazy val suffix: fastparse.noApi.Parser[PExp => PExp] =
    P(("." ~ idnuse).map { id => (e: PExp) => PFieldAccess(e, id) } |
      ("[.." ~/ exp ~ "]").map { n => (e: PExp) => PSeqTake(e, n) } |
      ("[" ~ exp ~ "..]").map { n => (e: PExp) => PSeqDrop(e, n) } |
      ("[" ~ exp ~ ".." ~ exp ~ "]").map { case (n, m) => (e: PExp) => PSeqDrop(PSeqTake(e, m), n) } |
      ("[" ~ exp ~ "]").map { e1 => (e0: PExp) => PSeqIndex(e0, e1) } |
      ("[" ~ exp ~ ":=" ~ exp ~ "]").map { case (i, v) => (e: PExp) => PSeqUpdate(e, i, v) })

  lazy val suffixExpr: P[PExp] = P((atom ~ suffix.rep).map { case (fac, ss) => foldPExp[PExp](fac, ss) })

  lazy val realSuffixExpr: P[PExp] = P((atom ~ suffix.rep).map { case (fac, ss) => foldPExp[PExp](fac, ss) })

  lazy val termOp: P[String] = P(StringIn("*", "/", "\\", "%").!)
  lazy val term: P[PExp] = P((suffixExpr ~ termd.rep).map { case (a, ss) => foldPExp[PExp](a, ss) })
  lazy val termd: P[PExp => PBinExp] = P(termOp ~ suffixExpr).map { case (op, id) => (e: PExp) => PBinExp(e, op, id) }
  lazy val sumOp: P[String] = P(StringIn("++", "+", "-").! | keyword("union").! | keyword("intersection").! | keyword("setminus").! | keyword("subset").!)
  lazy val sum: P[PExp] = P((term ~ sumd.rep).map { case (a, ss) => foldPExp[PBinExp](a, ss) })
  lazy val sumd: P[PExp => PBinExp] = P(sumOp ~ term).map { case (op, id) => (e: PExp) => PBinExp(e, op, id) }
  lazy val cmpOp = P(StringIn("<=", ">=", "<", ">").! | keyword("in").!)
//  lazy val cmpExp: P[PExp] = P((sum ~ cmpOp ~ cmpExp).map { case (a, b, c) => PBinExp(a, b, c) } | sum)
  lazy val cmpExp: P[PExp] = P(sum ~ (cmpOp ~ cmpExp).?).map{ case(a, b) => b match {
      case Some(c) => PBinExp(a, c._1,c._2 )
      case None => a
    }
  }
  lazy val eqOp = P(StringIn("==", "!=").!)
  lazy val eqExp: P[PExp] = P(cmpExp ~ (eqOp ~ eqExp).?).map { case (a, b) => b match {
        case Some(c) => PBinExp(a, c._1, c._2 )
        case None => a
      }
  }
  lazy val andExp: P[PExp] = P(eqExp ~ ("&&".! ~ andExp).?).map { case (a, b) => b match {
      case Some(c) => PBinExp(a, c._1, c._2 )
      case None => a
    }
  }
  lazy val orExp: P[PExp] = P(andExp ~ ("||".! ~ orExp).?).map { case (a, b) => b match {
      case Some(c) => PBinExp(a, c._1, c._2 )
      case None => a
    }
  }

  lazy val accessPred: P[PAccPred] = P(keyword("acc") ~/ ("(" ~ locAcc ~ ("," ~ exp).? ~ ")").map { case (loc, perms) => PAccPred(loc, perms.getOrElse(PFullPerm())) })
  lazy val locAcc: P[PLocationAccess] = P(fieldAcc | predAcc)
  //this rule is in doubt 2. Leaving an opaques symbol here
  lazy val fieldAcc: P[PFieldAccess] = P(realSuffixExpr.filter(getFieldAccess).map { case fa: PFieldAccess => fa })
  lazy val predAcc: P[PLocationAccess] = P(fapp)
//lazy val predAcc: P[PPredicateAccess] = P(idnuse ~ parens(actualArgList)).map { case (id, args) => PPredicateAccess(args, id) }
  //is it required to be one or more than 1 below
  lazy val actualArgList: P[Seq[PExp]] = P(exp.rep(sep = ","))
  lazy val inhaleExhale: P[PExp] = P("[" ~ exp ~ "," ~ exp ~ "]").map { case (a, b) => PInhaleExhaleExp(a, b) }
  lazy val perm: P[PExp] = P(keyword("none").map(_ => PNoPerm()) | keyword("wildcard").map(_ => PWildcard()) | keyword("write").map(_ => PFullPerm())
    | keyword("epsilon").map(_ => PEpsilon()) | ("perm" ~ parens(locAcc)).map(PCurPerm))
  //doubt (how is this working!!!! - Uses KIama Stuff :( )
  lazy val let: P[PExp] = P(
    ("let" ~/ idndef ~ "==" ~ "(" ~ exp ~ ")" ~ "in" ~ exp).map { case (id, exp1, exp2) =>
      /* Type unresolvedType is expected to be replaced with the type of exp1
       * after the latter has been resolved
       * */
      val unresolvedType = PUnknown().setPos(id)
      val formalArgDecl = PFormalArgDecl(id, unresolvedType).setPos(id)
      val nestedScope = PLetNestedScope(formalArgDecl, exp2).setPos(exp2)

      PLet(exp1, nestedScope)
    })
  lazy val idndef: P[PIdnDef] = P(ident).map(PIdnDef)

  lazy val quant: P[PExp] = P((keyword("forall") ~/ nonEmptyFormalArgList ~ "::" ~ trigger.rep ~ exp).map { case (a, b, c) => PForall(a, b, c) } |
    (keyword("exists") ~/ nonEmptyFormalArgList ~ "::" ~ exp).map { case (a, b) => PExists(a, b) })
  lazy val nonEmptyFormalArgList: P[Seq[PFormalArgDecl]] = P(formalArg.rep(min = 1, sep = ","))
  lazy val formalArg: P[PFormalArgDecl] = P(idndef ~ ":" ~ typ).map { case (a, b) => PFormalArgDecl(a, b) }
  //types
  lazy val typ: P[PType] = P(primitiveTyp | domainTyp | seqType | setType | multisetType)
  lazy val domainTyp: P[PDomainType] = P((idnuse ~ "[" ~ typ.rep(sep = ",") ~ "]").map { case (a, b) => PDomainType(a, b) } |
    idnuse.map {
      // domain type without type arguments (might also be a type variable)
      case name => PDomainType(name, Nil)
    })
  lazy val seqType: P[PType] = P(keyword("Seq") ~/ "[" ~ typ ~ "]").map(PSeqType)
  lazy val setType: P[PType] = P("Set" ~ "[" ~ typ ~ "]").map(PSetType)
  lazy val multisetType: P[PType] = P("Multiset" ~ "[" ~ typ ~ "]").map(PMultisetType)
  lazy val primitiveTyp: P[PType] = P(StringIn("Rational").!.map { case _ => PPrimitiv("Perm") } | StringIn("Int", "Bool", "Perm", "Ref").!.map(PPrimitiv))
  lazy val trigger: P[Seq[PExp]] = P("{" ~ exp.rep(sep = ",") ~ "}")
  //showing red but possibly correct checked on forperm [ ] hello::2*2
  lazy val forperm: P[PExp] = P(keyword("forperm") ~ "[" ~ idnuse.rep(sep = ",") ~ "]" ~ idndef ~ "::" ~ exp).map {
    case (ids, id, body) => PForPerm(PFormalArgDecl(id, PPrimitiv("Ref")), ids, body)
  }
  lazy val unfolding: P[PExp] = P(keyword("unfolding") ~/ predicateAccessPred ~ "in" ~ exp).map { case (a, b) => PUnfolding(a, b) }
  lazy val predicateAccessPred: P[PAccPred] = P(accessPred | predAcc.map { case loc => PAccPred(loc, PFullPerm()) })
  lazy val folding: P[PExp] = P(keyword("folding") ~/ predicateAccessPred ~ "in" ~ exp).map { case (a, b) => PFoldingGhostOp(a, b) }

  lazy val applying: P[PExp] =
  /*
    This is a inherited comment, will check this out

    We must be careful here to not create ambiguities in our grammar.
   * when 'magicWandExp' is used instead of the more specific
   * 'realMagicWandExp | idnuse', then the following problem can occur:
   * Consider an expression such as "applying w in A". The parser
   * will interpret "w in A" as a set-contains expression, which is
   * fine according to our rules. The outer applying-rule will the fail.
   * I suspect that NOT using a memoising packrat parser would help
   * here, because the failing applying-rule should backtrack enough
   * to reparse "w in A", but this time as desired, not as a
   * set-contains expression. This is just an assumption, however,
   * and implementing would mean that we have to rewrite the
   * left-recursive parsing rules (are these only sum and term?).
   * Moreover, not using a memoising parser might make the parser
   * significantly slower.
   */
//    P((("applying" ~/ "(" ~ realMagicWandExp ~ ")") | idnuse) ~ "in" ~ exp).map { case (a, b) => PApplyingGhostOp(a, b) }

  P("applying" ~ ("(" ~ realMagicWandExp ~ ")" | idnuse) ~ ("in" ~ exp)).map { case (a, b) => PApplyingGhostOp(a, b) }


  lazy val packaging: P[PExp] = /* See comment on applying */
    P("packaging" ~ ("(" ~ realMagicWandExp ~ ")" | idnuse) ~ "in" ~ exp).map { case (a, b) => PPackagingGhostOp(a, b) }
  lazy val setTypedEmpty: P[PExp] = P("Set" ~ "[" ~ typ ~ "]" ~ "(" ~ ")").map { case a => PEmptySet(a) }
  lazy val explicitSetNonEmpty: P[PExp] = P("Set" /*~ opt("[" ~> typ <~ "]")*/ ~ "(" ~ exp.rep(sep = ",") ~ ")").map(PExplicitSet)
  lazy val explicitMultisetNonEmpty: P[PExp] = P("Multiset" ~ "(" ~/ exp.rep(min = 1, sep = ",") ~ ")").map { case elems => PExplicitMultiset(elems) }
  lazy val multiSetTypedEmpty: P[PExp] = P("Multiset" ~ "[" ~/ typ ~ "]" ~ "(" ~ ")").map(PEmptyMultiset)
  lazy val seqTypedEmpty: P[PExp] = P("Seq[" ~ typ ~ "]()").map(PEmptySeq)
  lazy val seqLength: P[PExp] = P("|" ~ exp ~ "|").map(PSize)
  lazy val explicitSeqNonEmpty: P[PExp] = P("Seq(" ~ exp.rep(min = 1, sep = ",") ~ ")").map {
    //      case Nil => PEmptySeq(PUnknown())
    case elems => PExplicitSeq(elems)
  }
  lazy val seqRange: P[PExp] = P("[" ~ exp ~ ".." ~ exp ~ ")").map { case (a, b) => { PRangeSeq(a, b) } }
  lazy val fapp: P[PFunctApp] = P(idnuse ~ parens(actualArgList)).map {
    case (func, args) => PFunctApp(func, args, None)
  }
  lazy val typedFapp: P[PExp] = P(parens(idnuse ~ parens(actualArgList) ~ ":" ~ typ)).map {
    case (func, args, typeGiven) => PFunctApp(func, args, Some(typeGiven))
  }


  //  Statemnts
  lazy val stmt: P[PStmt] = P(fieldassign | localassign | fold | unfold | exhale | assertP |
    inhale | ifthnels | whle | varDecl | defineDecl | letwandDecl | newstmt | fresh | constrainingBlock |
    methodCall | goto | lbl | packageWand | applyWand)

  lazy val fieldassign: P[PFieldAssign] = P(fieldAcc ~ ":=" ~ exp).map { case (a, b) => PFieldAssign(a, b) }
  lazy val localassign: P[PVarAssign] = P(idnuse ~ ":=" ~ exp).map { case (a, b) => PVarAssign(a, b) }
  lazy val fold: P[PFold] = P("fold" ~ predicateAccessPred).map(PFold)
  lazy val unfold: P[PUnfold] = P("unfold" ~ predicateAccessPred).map(PUnfold)
  lazy val exhale: P[PExhale] = P(keyword("exhale") ~/ exp).map(PExhale)
  lazy val assertP: P[PAssert] = P(keyword("assert") ~/ exp).map(PAssert)
  lazy val inhale: P[PInhale] = P((keyword("inhale") | keyword("assume")) ~ exp).map(PInhale)
  lazy val ifthnels: P[PIf] = P("if" ~ "(" ~ exp ~ ")" ~ block ~ elsifEls).map {
    case (cond, thn, ele) => PIf(cond, PSeqn(thn), ele)
  }
  lazy val block: P[Seq[PStmt]] = P("{" ~ stmts ~ "}")
  lazy val stmts: P[Seq[PStmt]] = P(stmt ~ ";".?).rep
  lazy val elsifEls: P[PStmt] = P(elsif | els)
  lazy val elsif: P[PStmt] = P("elseif" ~/ "(" ~ exp ~ ")" ~ block ~ elsifEls).map {
    case (cond, thn, ele) => PIf(cond, PSeqn(thn), ele)
  }
  lazy val els: P[PStmt] = ("else" ~ block).?.map { block => PSeqn(block.getOrElse(Nil)) }
  lazy val whle: P[PWhile] = P("while" ~ "(" ~ exp ~ ")" ~ inv.rep ~ block).map {
    case (cond, invs, body) => PWhile(cond, invs, PSeqn(body))
  }
  lazy val inv: P[PExp] = P(keyword("invariant") ~ exp ~ ";".?)
  lazy val varDecl: P[PLocalVarDecl] = P(keyword("var") ~/ idndef ~ ":" ~ typ ~ (":=" ~ exp).?).map { case (a, b, c) => PLocalVarDecl(a, b, c) }

 /* lazy val defineDecl =
    ("define" ~> idndef) ~ opt("(" ~> repsep(idndef, ",") <~ ")") ~ (exp | block) ^^ {
      case iddef ~ args ~ (e: PExp) => PDefine(iddef, args, e)
      case iddef ~ args ~ (ss: Seq[PStmt] @unchecked) => PDefine(iddef, args, PSeqn(ss))
    }*/
  lazy val defineDecl: P[PDefine] = P(keyword("define") ~/ idndef ~ ("(" ~ idndef.rep(sep = ",") ~ ")").? ~ (exp|block)).map {
    case (a, b, c) => c match {
      case e: PExp => PDefine(a,b,e)
      case ss: Seq[PStmt] @unchecked => PDefine(a,b,PSeqn(ss))
    }



  }
  lazy val letwandDecl: P[PLetWand] = P(keyword("wand") ~/ idndef ~ ":=" ~ exp).map { case (a, b) => PLetWand(a, b) }
  lazy val newstmt: P[PNewStmt] = P(idnuse ~ ":=" ~ "new" ~ "(" ~ starOrFields ~ ")").map { case (a, b) => PNewStmt(a, b) }
  //doubt see what happened here later on (had to add .! in first case)
  lazy val starOrFields: P[Option[Seq[PIdnUse]]] = P(("*").!.map { _ => None } | (idnuse.rep(sep = ",").map { fields => Some(fields) }))
  lazy val fresh: P[PFresh] = P("fresh" ~ idnuse.rep(sep = ",")).map { case vars => PFresh(vars) }
  lazy val constrainingBlock: P[PConstraining] = P("constraining" ~ "(" ~ idnuse.rep(sep = ",") ~ ")" ~ block).map { case (vars, s) => PConstraining(vars, PSeqn(s)) }
  lazy val methodCall: P[PMethodCall] = P((idnuse.rep(sep = ",") ~ ":=").? ~ idnuse ~ parens(exp.rep(sep = ","))).map {
    case (None, method, args) => PMethodCall(Nil, method, args)
    case (Some(targets), method, args) => PMethodCall(targets, method, args)
  }
  lazy val goto: P[PGoto] = P("goto" ~/ idnuse).map(PGoto)
  lazy val lbl: P[PLabel] = P(keyword("label") ~/ idndef).map(PLabel)
  lazy val packageWand: P[PPackageWand] = P("package" ~/ magicWandExp).map(PPackageWand)
  lazy val applyWand: P[PApplyWand] = P("apply" ~/ magicWandExp).map(PApplyWand)

  // Declarations

  lazy val programDecl: P[PProgram] = P((preambleImport | defineDecl | domainDecl | fieldDecl | functionDecl | predicateDecl | methodDecl).rep).map {
    case decls =>
      var globalDefines: Seq[PDefine] = decls.collect { case d: PDefine => d }
      globalDefines = expandDefines(globalDefines, globalDefines)

      val imports: Seq[PImport] = decls.collect { case i: PImport => i }

      val dups: Iterable[viper.silver.verifier.ParseError] = imports.groupBy(identity).collect {
        case (imp@PImport(x), List(_, _, _*)) =>
          val dup_pos = imp.start.asInstanceOf[viper.silver.ast.Position]
          val report = s"""multiple imports of the same file "$x" detected"""
          //println(s"warning: $report ($dup_pos)")
          viper.silver.verifier.ParseError(report, dup_pos)
      }

      //println(s"imports in current file: $imports")
      //println(s"all imports: ${viper.silver.parser.Parser._imports}")

      val imp_progs_results: Seq[Either[ParseReport, Any] with Product with Serializable] = imports.collect {
        case imp@PImport(imp_file) =>
          val imp_path = java.nio.file.Paths.get(file.getParent + "/" + imp_file)
          val imp_pos = imp.start.asInstanceOf[viper.silver.ast.Position]

          if (java.nio.file.Files.notExists(imp_path))
            Left(viper.silver.verifier.ParseError(s"""file "$imp_path" does not exist""", imp_pos))

          else if (java.nio.file.Files.isSameFile(imp_path, file))
            Left(viper.silver.verifier.ParseError(s"""importing yourself is probably not a good idea!""", imp_pos))

          else if (_imports.put(imp_path, true).isEmpty) {
            val source = scala.io.Source.fromFile(imp_path.toString)
            val buffer = try {
              Right(source.getLines.toArray)
            } catch {
              case e@(_: RuntimeException | _: java.io.IOException) =>
                Left(viper.silver.verifier.ParseError(s"""could not import file ($e)""", imp_pos))
            } finally {
              source.close()
            }
            buffer match {
              case Left(e) => Left(e)
              case Right(s) =>
                //TODO print debug info iff --dbg switch is used
                //println(s"@importing $imp_file into $file")

                val p = RecParser(imp_path).parses(s.mkString("\n") + "\n")
                p match {
                  case fastparse.core.Parsed.Success(a, _) => Right(a)
                  case fastparse.core.Parsed.Failure(msg, next, extra) => Left(viper.silver.verifier.ParseError(s"Failure: $msg", PFilePosition(imp_path, extra.line, extra.col)))
//                  case p.Error(msg, next) => Left(viper.silver.verifier.ParseError(s"Error: $msg", PFilePosition(imp_path, next.pos.line, next.pos.column)))
                }
            }
          }

          else {
            val report = s"found loop dependency among these imports:\n" +
              _imports.map { case (k, v) => k }.mkString("\n")
            println(s"warning: $report\n(loop starts at $imp_pos)")
            Right(ParseWarning(report, imp_pos))
          }
      }

      val imp_progs = imp_progs_results.collect { case Right(p) => p }

      val imp_reports = imp_progs_results.collect { case Left(e) => e } ++
        imp_progs.collect { case PProgram(_, _, _, _, _, _, e: List[ParseReport]) => e }.flatten ++
        dups

      val files =
        imp_progs.collect { case PProgram(f: Seq[PImport], _, _, _, _, _, _) => f }.flatten ++
          imports

      val domains =
        imp_progs.collect { case PProgram(_, d: Seq[PDomain], _, _, _, _, _) => d }.flatten ++
          decls.collect { case d: PDomain => expandDefines(globalDefines, d) }

      val fields =
        imp_progs.collect { case PProgram(_, _, f: Seq[PField], _, _, _, _) => f }.flatten ++
          decls.collect { case f: PField => f }

      val functions =
        imp_progs.collect { case PProgram(_, _, _, f: Seq[PFunction], _, _, _) => f }.flatten ++
          decls.collect { case d: PFunction => expandDefines(globalDefines, d) }

      val predicates =
        imp_progs.collect { case PProgram(_, _, _, _, p: Seq[PPredicate], _, _) => p }.flatten ++
          decls.collect { case d: PPredicate => expandDefines(globalDefines, d) }

      val methods =
        imp_progs.collect { case PProgram(_, _, _, _, _, m: Seq[PMethod], _) => m }.flatten ++
          decls.collect {
            case meth: PMethod =>
              var localDefines = meth.deepCollect { case n: PDefine => n }
              localDefines = expandDefines(localDefines ++ globalDefines, localDefines)

              val methWithoutDefines =
                if (localDefines.isEmpty)
                  meth
                else
                  meth.transform { case la: PDefine => PSkip().setPos(la) }()

              expandDefines(localDefines ++ globalDefines, methWithoutDefines)
          }

      PProgram(files, domains, fields, functions, predicates, methods, imp_reports)
  }
  lazy val preambleImport: P[PImport] = P(keyword("import") ~/ quoted(relativeFilePath)).map { case filename => PImport(filename) }
  //chek if this is a correct regex doubt
  lazy val relativeFilePath: P[String] = P(("A" ~~ CharIn("~.").?).! ~~ (CharIn("/").? ~~ CharIn(".", 'A' to 'Z', 'a' to 'z', '0' to '9', "_- \n\t")).rep(1))
  lazy val domainDecl: P[PDomain] = P("domain" ~/ idndef ~ ("[" ~ domainTypeVarDecl.rep(sep = ",") ~ "]").? ~ "{" ~ domainFunctionDecl.rep ~
    axiomDecl.rep ~ "}").map {
    case (name, typparams, funcs, axioms) =>
      PDomain(
        name,
        typparams.getOrElse(Nil),
        funcs map (f => PDomainFunction(f.idndef, f.formalArgs, f.typ, f.unique)(PIdnUse(name.name)).setPos(f)),
        axioms map (a => PAxiom(a.idndef, a.exp)(PIdnUse(name.name)).setPos(a)))
  }
  lazy val domainTypeVarDecl: P[PTypeVarDecl] = P(idndef).map(PTypeVarDecl)
  lazy val domainFunctionDecl: P[PDomainFunction1] = P("unique".!.? ~ functionSignature ~ ";".?).map {
    case (unique, fdecl) => fdecl match {
      case (name, formalArgs, t) => PDomainFunction1(name, formalArgs, t, unique.isDefined)
    }
  }
  lazy val functionSignature = P("function" ~ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ)
  lazy val formalArgList: P[Seq[PFormalArgDecl]] = P( formalArg.rep(sep = ","))
  lazy val axiomDecl: P[PAxiom1] = P(keyword("axiom") ~ idndef ~ "{" ~ exp ~ "}" ~ ";".?).map { case (a, b) => PAxiom1(a, b) }
  lazy val fieldDecl: P[PField] = P("field" ~/ idndef ~ ":" ~ typ ~ ";".?).map { case (a, b) => PField(a, b) }
  lazy val functionDecl: P[PFunction] = P("function" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
    post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, c, d, e, f) => PFunction(a, b, c, d, e, f) }

  lazy val pre: P[PExp] = P("requires" ~/ exp ~ ";".?)
  lazy val post: P[PExp] = P("ensures" ~/ exp ~ ";".?)

  lazy val predicateDecl: P[PPredicate] = P("predicate" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ("{" ~ exp ~ "}").?).map { case (a, b, c) => PPredicate(a, b, c) }
  lazy val methodDecl: P[PMethod] = P(methodSignature ~/ pre.rep ~ post.rep ~ block.?).map {
    case (name, args, rets, pres, posts, Some(body)) =>
      PMethod(name, args, rets.getOrElse(Nil), pres, posts, PSeqn(body))
    case (name, args, rets, pres, posts, None) =>
      PMethod(name, args, rets.getOrElse(Nil), pres, posts, PSeqn(Seq(PInhale(PBoolLit(b = false)))))
  }
  lazy val methodSignature = P("method" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ("returns" ~ "(" ~ formalArgList ~ ")").?)
  lazy val fastparser: P[PProgram] = P( Start ~ programDecl ~ End)


  /*
  *
  *
  *
  *
  *
  *
  *
  *
  *
  *
  *
  *
  *
  *
  * */







def main(args: Array[String]) {
//  println(fastparser.parse("var newK$_1: Perm\n  this_1 := __this_1\n  in_1 := __in_1\n  out_1 := __out_1\n  n$_3 := new(*)\n  __flatten_1 := n$_3\n  fresh newK$_1"))
  println(FastParser.parse("define B(x, res) true\n\nmethod test1(y: Ref, n: Ref)\n    ensures B(y)\n    {}", file))
//  println(exp.parse("[0..|nodes|)"))
}
}
