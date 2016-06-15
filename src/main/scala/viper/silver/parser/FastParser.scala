package viper.silver.parser

/**
  * Created by sahil on 24.05.16.
  */

import java.nio.file.Path

import fastparse.Implicits.Sequencer
import fastparse.parsers.Combinators.{Rule, Sequence}
import fastparse.WhitespaceApi
import fastparse.all._
import fastparse.core.Parsed.Position
import fastparse.parsers.Intrinsics
import fastparse.core.{Mutable, ParseCtx, Parsed, Parser}
import fastparse.parsers.{Intrinsics, Terminals}
import org.kiama.util.Positions
import org.kiama.util.Positions._
import viper.silver.ast.HasLineColumn

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
        setStart (value0, PFilePosition(file, start0._1, start0._2))
        setFinish (value0, PFilePosition(file, end0._1, end0._2))
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
                setStart (value2, PFilePosition(file, start1._1, start1._2))
                setFinish (value2, PFilePosition(file, end1._1, end1._2))
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
          setStart (s.value, PFilePosition(file, start._1, start._2))
          setFinish (s.value, PFilePosition(file, end._1, end._2))
          //          println(file)
          s
      }
    } else {
      lazy val res = pCached.parseRec(cfg, index) match{
        case f: Mutable.Failure => failMore(f, index, cfg.logDepth)
        case s: Mutable.Success[T] => {
          val start = computeFrom(cfg.input, index)
          val end = computeFrom(cfg.input, s.index)
          setStart (s.value, PFilePosition(file, start._1, start._2))
          setFinish (s.value, PFilePosition(file, end._1, end._2))
          s
        }
      }
      cfg.instrument(this, index, () => res.toResult)
      res
    }
  }
}





object FastParser {

  var _file: Path = null

  def P[T](p: => Parser[T])(implicit name: sourcecode.Name): Parser[T] =
    new PositionRule(name.value, () => p, _file)

  def PWrapper(WL: P0) = new PWrapper(WL)
  class PWrapper(WL: P0){
    implicit def parserApi[T, V](p0: T)(implicit c: T => P[V]): WhitespaceApi[V] =
      new WhitespaceApi[V](p0, WL){
        //        override def ~[V, R](p: P[V])
        //                            (implicit ev: Sequencer[T, V, R])
        //        : P[R] = {
        //          assert(p != null)
        //          new WhitespaceApi.CustomSequence(WL, if (p0 != WL) p0 else Pass.asInstanceOf[P[T]], p, cut=false)(ev)
        //        }

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
  def keyword(check: String) = check ~~ !CharIn('0' to '9', 'A' to 'Z', 'a' to 'z')

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

    def lookupOrElse(piu: PIdnUse, els: PExp) =
      defines.find(_.idndef.name == piu.name).fold[PExp](els) _

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

            define.exp
          })

        case fapp: PFunctApp =>
          /* Potentially expand a named assertion that takes arguments, e.g. A(x, y) */
          lookupOrElse(fapp.func, fapp)(define => define.args match {
            case None =>
              /* There is a named assertion with name `func`, but the named
               * assertion takes arguments. Hence, the fapp cannot denote the
               * use of a named assertion.
               */
              fapp
            case Some(args) if fapp.args.length != args.length =>
              /* Similar to the previous case */
              fapp
            case Some(args) =>
              expanded = true

              define.exp.transform {
                /* Expand the named assertion's formal arguments by the given actual arguments */
                case piu: PIdnUse =>
                  args.indexWhere(_.name == piu.name) match {
                    case -1 => piu
                    case i => fapp.args(i)
                  }
              }(): PExp /* [2014-06-31 Malte] Type-checker wasn't pleased without it */
          })
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
  lazy val predAcc: P[PPredicateAccess] = P(idnuse ~ parens(actualArgList)).map { case (id, args) => PPredicateAccess(args, id) }
  //is it required to be one or more than 1 below
  lazy val actualArgList: P[Seq[PExp]] = P(exp).rep(sep = ",")
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
    (keyword("exists") ~ nonEmptyFormalArgList ~ "::" ~ exp).map { case (a, b) => PExists(a, b) })
  lazy val nonEmptyFormalArgList: P[Seq[PFormalArgDecl]] = P(formalArg.rep(sep = ","))
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
  lazy val seqRange: P[PExp] = P("[" ~ exp ~ ".." ~ exp ~ ")").map { case (a, b) => {
//    println("we are here")
    PRangeSeq(a, b)
  } }
  lazy val fapp: P[PExp] = P(idnuse ~ parens(actualArgList)).map {
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
  lazy val defineDecl: P[PDefine] = P(keyword("define") ~/ idndef ~ ("(" ~ idndef.rep(sep = ",") ~ ")").? ~ exp).map { case (a, b, c) => PDefine(a, b, c) }
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

          else if (viper.silver.parser.Parser._imports.put(imp_path, true).isEmpty) {
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

                val p = viper.silver.parser.Parser.RecParser(imp_path)
                p.parse(s.mkString("\n") + "\n") match {
                  case p.Success(a, _) => Right(a)
                  case p.Failure(msg, next) => Left(viper.silver.verifier.ParseError(s"Failure: $msg", PFilePosition(imp_path, next.pos.line, next.pos.column)))
                  case p.Error(msg, next) => Left(viper.silver.verifier.ParseError(s"Error: $msg", PFilePosition(imp_path, next.pos.line, next.pos.column)))
                }
            }
          }

          else {
            val report = s"found loop dependency among these imports:\n" +
              viper.silver.parser.Parser._imports.map { case (k, v) => k }.mkString("\n")
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
  lazy val formalArgList: P[Seq[PFormalArgDecl]] = P(formalArg.rep(sep = ","))
  lazy val axiomDecl: P[PAxiom1] = P("axiom" ~ idndef ~ "{" ~ exp ~ "}" ~ ";".?).map { case (a, b) => PAxiom1(a, b) }
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
  println(fastparser.parse("field foo: Int\n\nmethod specialVariables()\n{\n  var resulter: Ref\n\n  resulter := new(foo)\n\n  resulter.foo := 1\n}\n\nmethod types()\n{\n  var Inter: Ref\n  var Permer: Ref\n  var Booler: Ref\n  var Refer: Ref\n\n  Inter := new(foo)\n  Permer := new(foo)\n  Booler := new(foo)\n  Refer := new(foo)\n\n  Inter.foo := 1\n  Permer.foo := 1\n  Booler.foo := 1\n  Refer.foo := 1\n}\n\nmethod booleanConstants()\n{\n  var trueer: Ref\n  var falseer: Ref\n\n  trueer := new(foo)\n  falseer := new(foo)\n\n  trueer.foo := 1\n  falseer.foo := 1\n}\n\nmethod nulll()\n{\n  var nuller: Ref\n\n  nuller := new(foo)\n\n  nuller.foo := 1\n}\n\nmethod declarationKeywords()\n{\n  var methoder: Ref\n  var functioner: Ref\n  var predicateer: Ref\n  var programer: Ref\n  var domainer: Ref\n  var axiomer: Ref\n  var varer: Ref\n  var returnser: Ref\n  var fielder: Ref\n  var defineer: Ref\n\n  methoder := new(foo)\n  functioner := new(foo)\n  predicateer := new(foo)\n  programer := new(foo)\n  domainer := new(foo)\n  axiomer := new(foo)\n  varer := new(foo)\n  returnser := new(foo)\n  fielder := new(foo)\n  defineer := new(foo)\n\n  methoder.foo := 1\n  functioner.foo := 1\n  predicateer.foo := 1\n  programer.foo := 1\n  domainer.foo := 1\n  axiomer.foo := 1\n  varer.foo := 1\n  returnser.foo := 1\n  fielder.foo := 1\n  defineer.foo := 1\n}\n\nmethod specifications()\n{\n  var requireser: Ref\n  var ensureser: Ref\n  var invarianter: Ref\n\n  requireser := new(foo)\n  ensureser := new(foo)\n  invarianter := new(foo)\n\n  requireser.foo := 1\n  ensureser.foo := 1\n  invarianter.foo := 1\n}\n\nmethod statements()\n{\n  var folder: Ref\n  var unfolder: Ref\n  var inhaleer: Ref\n  var exhaleer: Ref\n  var newer: Ref\n  var asserter: Ref\n  var assumeer: Ref\n  var gotoer: Ref\n\n  folder := new(foo)\n  unfolder := new(foo)\n  inhaleer := new(foo)\n  exhaleer := new(foo)\n  newer := new(foo)\n  asserter := new(foo)\n  assumeer := new(foo)\n  gotoer := new(foo)\n\n  folder.foo := 1\n  unfolder.foo := 1\n  inhaleer.foo := 1\n  exhaleer.foo := 1\n  newer.foo := 1\n  asserter.foo := 1\n  assumeer.foo := 1\n  gotoer.foo := 1\n}\n\nmethod controlStructures()\n{\n  var whileer: Ref\n  var ifer: Ref\n  var elseifer: Ref\n  var elseer: Ref\n\n  whileer := new(foo)\n  ifer := new(foo)\n  elseifer := new(foo)\n  elseer := new(foo)\n\n  whileer.foo := 1\n  ifer.foo := 1\n  elseifer.foo := 1\n  elseer.foo := 1\n}\n\nmethod specialFreshBlock()\n{\n  var fresher: Ref\n  var constraininger: Ref\n\n  fresher := new(foo)\n  constraininger := new(foo)\n\n  fresher.foo := 1\n  constraininger.foo := 1\n}\n\nmethod sequences()\n{\n  var Seqer: Ref\n\n  Seqer := new(foo)\n\n  Seqer.foo := 1\n}\n\nmethod setsAndMultisets()\n{\n  var Seter: Ref\n  var Multiseter: Ref\n  var unioner: Ref\n  var intersectioner: Ref\n  var setminuser: Ref\n  var subseter: Ref\n\n  Seter := new(foo)\n  Multiseter := new(foo)\n  unioner := new(foo)\n  intersectioner := new(foo)\n  setminuser := new(foo)\n  subseter := new(foo)\n\n  Seter.foo := 1\n  Multiseter.foo := 1\n  unioner.foo := 1\n  intersectioner.foo := 1\n  setminuser.foo := 1\n  subseter.foo := 1\n}\n\nmethod proverHintExpressions()\n{\n  var unfoldinger: Ref\n  var iner: Ref\n\n  unfoldinger := new(foo)\n  unfoldinger.foo := 1\n  iner := new(foo)\n  iner.foo := 1\n}\n\nmethod oldExpression()\n{\n  var older: Ref\n\n  older := new(foo)\n  older.foo := 1\n}\n\nmethod quantification()\n{\n  var foraller: Ref\n  var existser: Ref\n\n  foraller := new(foo)\n  foraller.foo := 1\n  existser := new(foo)\n  existser.foo := 1\n}\n\nmethod permissionSyntax()\n{\n  var accer: Ref\n  var wildcarder: Ref\n  var writer: Ref\n  var noneer: Ref\n  var epsiloner: Ref\n  var permer: Ref\n\n  accer := new(foo)\n  accer.foo := 1\n  wildcarder := new(foo)\n  wildcarder.foo := 1\n  writer := new(foo)\n  writer.foo := 1\n  noneer := new(foo)\n  noneer.foo := 1\n  epsiloner := new(foo)\n  epsiloner.foo := 1\n  permer := new(foo)\n  permer.foo := 1\n}\n\nmethod modifiers()\n{\n  var uniqueer: Ref\n\n  uniqueer := new(foo)\n  uniqueer.foo := 1\n}"))
//  println(exp.parse("[0..|nodes|)"))
}
}
