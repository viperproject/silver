package viper.silver.parser

/**
  * Created by sahil on 24.05.16.
  */

import java.nio.file.Path

import fastparse.parsers.Combinators.Rule
import fastparse.WhitespaceApi
import fastparse.core.Parsed.Position
import fastparse.parsers.Intrinsics
import fastparse.core.{Mutable, ParseCtx, Parser}
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


class PositionRule[+T](override val name: String, override val p: () => Parser[T], file: Path) extends Rule[T](name, p){
  lazy val pCached = p()
  override def parseRec(cfg: ParseCtx, index: Int) = {


    def computeFrom(input: String, index: Int) : (Int, Int) = {
      val lines = input.take(1 + index).lines.toVector
      val line = lines.length
      val col = lines.lastOption.map(_.length).getOrElse(0)
      Pair(line, col)
    }
    if (cfg.instrument == null) {
      pCached.parseRec(cfg, index) match{
        case f: Mutable.Failure => failMore(f, index, cfg.logDepth)
        case s: Mutable.Success[T] =>
          val start = computeFrom(cfg.input, index)
          val end = computeFrom(cfg.input, s.index)
          setStart (s.value, PFilePosition(file, start._1, start._2))
          setFinish (s.value, PFilePosition(file, end._1, end._2))
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

  val White = WhitespaceApi.Wrapper {
    import fastparse.all._

    NoTrace((("/*" ~ (AnyChar ~ !StringIn("*/")).rep ~ AnyChar ~ "*/") | ("//" ~ CharsWhile(_ != '\n') ~ "\n") | " " | "\t" | "\n").rep)
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

  lazy val integer = P(CharIn('0' to '9').rep(1)).!.map { s => PIntLit(BigInt(s)) }
  lazy val booltrue = P(keyword("true")).map(_ => PBoolLit(b = true))
  lazy val boolfalse = P(keyword("false")).map(_ => PBoolLit(b = false))
  lazy val nul = P(keyword("null")).map(_ => PNullLit())

  lazy val identifier = P(CharIn('A' to 'Z', 'a' to 'z', "$_") ~~ CharIn('0' to '9', 'A' to 'Z', 'a' to 'z', "$_").repX)
  lazy val ident = P(identifier.!).filter{case a => !keywords.contains(a)}
  //possible customize error code in rule ident
  lazy val idnuse: P[PIdnUse] = P(ident).map(PIdnUse)

  lazy val old: P[PExp] = P((StringIn("old") ~ parens(exp)).map(POld) | ("[" ~ idnuse ~ "]" ~ parens(exp)).map { case (a, b) => PLabelledOld(a, b) })
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

  lazy val termOp = P(StringIn("*", "/", "\\", "%").!)
  lazy val term: P[PExp] = P((suffixExpr ~ termd.rep).map { case (a, ss) => foldPExp[PExp](a, ss) })
  lazy val termd: P[PExp => PBinExp] = P(termOp ~ suffixExpr).map { case (op, id) => (e: PExp) => PBinExp(e, op, id) }
  lazy val sumOp = P(StringIn("++", "+", "-").! | keyword("union").! | keyword("intersection").! | keyword("setminus").! | keyword("subset").!)
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

  lazy val accessPred: P[PAccPred] = P(StringIn("acc") ~/ ("(" ~ locAcc ~ ("," ~ exp).? ~ ")").map { case (loc, perms) => PAccPred(loc, perms.getOrElse(PFullPerm())) })
  lazy val locAcc: P[PLocationAccess] = P(fieldAcc | predAcc)
  //this rule is in doubt :D 2. Leaving an opaques symbol here
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
  lazy val idndef = P(ident).map(PIdnDef)

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
  lazy val seqType: P[PType] = P("Seq" ~/ "[" ~ typ ~ "]").map(PSeqType)
  lazy val setType: P[PType] = P("Set" ~ "[" ~ typ ~ "]").map(PSetType)
  lazy val multisetType: P[PType] = P("Multiset" ~ "[" ~ typ ~ "]").map(PMultisetType)
  lazy val primitiveTyp: P[PType] = P(StringIn("Rational")).!.map { case _ => PPrimitiv("Perm") } | StringIn("Int", "Bool", "Perm", "Ref").!.map(PPrimitiv)
  lazy val trigger: P[Seq[PExp]] = P("{" ~ exp.rep(sep = ",") ~ "}")
  //showing red but possibly correct checked on forperm [ ] hello::2*2
  lazy val forperm: P[PExp] = P(keyword("forperm") ~ "[" ~ idnuse.rep(sep = ",") ~ "]" ~ idndef ~ "::" ~ exp).map {
    case (ids, id, body) => PForPerm(PFormalArgDecl(id, PPrimitiv("Ref")), ids, body)
  }
  lazy val unfolding: P[PExp] = P("unfolding" ~/ predicateAccessPred ~ "in" ~ exp).map { case (a, b) => PUnfolding(a, b) }
  lazy val predicateAccessPred: P[PAccPred] = P(accessPred | predAcc.map { case loc => PAccPred(loc, PFullPerm()) })
  lazy val folding: P[PExp] = P("folding" ~/ predicateAccessPred ~ "in" ~ exp).map { case (a, b) => PFoldingGhostOp(a, b) }

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
  lazy val stmt = P(fieldassign | localassign | fold | unfold | exhale | assert |
    inhale | ifthnels | whle | varDecl | defineDecl | letwandDecl | newstmt | fresh | constrainingBlock |
    methodCall | goto | lbl | packageWand | applyWand)

  lazy val fieldassign = P(fieldAcc ~ ":=" ~ exp).map { case (a, b) => PFieldAssign(a, b) }
  lazy val localassign = P(idnuse ~ ":=" ~ exp).map { case (a, b) => PVarAssign(a, b) }
  lazy val fold = P("fold" ~ predicateAccessPred).map(PFold)
  lazy val unfold = P("unfold" ~ predicateAccessPred).map {
    PUnfold
  }
  lazy val exhale = P(keyword("exhale") ~/ exp).map(PExhale)
  lazy val assert = P(keyword("assert") ~/ exp).map(PAssert)
  lazy val inhale = P((keyword("inhale") | keyword("assume")) ~ exp).map(PInhale)
  lazy val ifthnels = P("if" ~ "(" ~ exp ~ ")" ~ block ~ elsifEls).map {
    case (cond, thn, ele) => PIf(cond, PSeqn(thn), ele)
  }
  lazy val block: P[Seq[PStmt]] = P("{" ~ stmts ~ "}")
  lazy val stmts = P(stmt ~ ";".?).rep
  lazy val elsifEls: P[PStmt] = P(elsif | els)
  lazy val elsif: P[PStmt] = P("elseif" ~/ "(" ~ exp ~ ")" ~ block ~ elsifEls).map {
    case (cond, thn, ele) => PIf(cond, PSeqn(thn), ele)
  }
  lazy val els: P[PStmt] = ("else" ~ block).?.map { block => PSeqn(block.getOrElse(Nil)) }
  lazy val whle = P("while" ~ "(" ~ exp ~ ")" ~ inv.rep ~ block).map {
    case (cond, invs, body) => PWhile(cond, invs, PSeqn(body))
  }
  lazy val inv = P("invariant" ~ exp ~ ";".?)
  lazy val varDecl = P("var" ~/ idndef ~ ":" ~ typ ~ (":=" ~ exp).?).map { case (a, b, c) => PLocalVarDecl(a, b, c) }
  lazy val defineDecl = P("define" ~/ idndef ~ ("(" ~ idndef.rep(sep = ",") ~ ")").? ~ exp).map { case (a, b, c) => PDefine(a, b, c) }
  lazy val letwandDecl = P("wand" ~/ idndef ~ ":=" ~ exp).map { case (a, b) => PLetWand(a, b) }
  lazy val newstmt = P(idnuse ~ ":=" ~ "new" ~ "(" ~ starOrFields ~ ")").map { case (a, b) => PNewStmt(a, b) }
  //doubt see what happened here later on (had to add .! in first case)
  lazy val starOrFields = P(("*").!.map { _ => None } | idnuse.rep(sep = ",").map { fields => Some(fields) })
  lazy val fresh = P("fresh" ~ idnuse.rep(sep = ",")).map { case vars => PFresh(vars) }
  lazy val constrainingBlock = P("constraining" ~ "(" ~ idnuse.rep(sep = ",") ~ ")" ~ block).map { case (vars, s) => PConstraining(vars, PSeqn(s)) }
  lazy val methodCall = P((idnuse.rep(sep = ",") ~ ":=").? ~ idnuse ~ parens(exp.rep(sep = ","))).map {
    case (None, method, args) => PMethodCall(Nil, method, args)
    case (Some(targets), method, args) => PMethodCall(targets, method, args)
  }
  lazy val goto = P("goto" ~/ idnuse).map(PGoto)
  lazy val lbl = P(keyword("label") ~/ idndef).map(PLabel)
  lazy val packageWand = P("package" ~/ magicWandExp).map(PPackageWand)
  lazy val applyWand = P("apply" ~/ magicWandExp).map(PApplyWand)

  // Declarations

  lazy val programDecl = P((preambleImport | defineDecl | domainDecl | fieldDecl | functionDecl | predicateDecl | methodDecl).rep).map {
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
                  case p.Failure(msg, next) => Left(viper.silver.verifier.ParseError(s"Failure: $msg", FilePosition(imp_path, next.pos)))
                  case p.Error(msg, next) => Left(viper.silver.verifier.ParseError(s"Error: $msg", FilePosition(imp_path, next.pos)))
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
  lazy val preambleImport = P(keyword("import") ~/ quoted(relativeFilePath)).map { case filename => PImport(filename) }
  //chek if this is a correct regex doubt
  lazy val relativeFilePath = P(("A" ~~ CharIn("~.").?).! ~~ (CharIn("/").? ~~ CharIn(".", 'A' to 'Z', 'a' to 'z', '0' to '9', "_- \n\t")).rep(1))
  lazy val domainDecl = P("domain" ~/ idndef ~ ("[" ~ domainTypeVarDecl.rep(sep = ",") ~ "]").? ~ "{" ~ domainFunctionDecl.rep ~
    axiomDecl.rep ~ "}").map {
    case (name, typparams, funcs, axioms) =>
      PDomain(
        name,
        typparams.getOrElse(Nil),
        funcs map (f => PDomainFunction(f.idndef, f.formalArgs, f.typ, f.unique)(PIdnUse(name.name)).setPos(f)),
        axioms map (a => PAxiom(a.idndef, a.exp)(PIdnUse(name.name)).setPos(a)))
  }
  lazy val domainTypeVarDecl = P(idndef).map(PTypeVarDecl)
  lazy val domainFunctionDecl = P("unique".!.? ~ functionSignature ~ ";".?).map {
    case (unique, fdecl) => fdecl match {
      case (name, formalArgs, t) => PDomainFunction1(name, formalArgs, t, unique.isDefined)
    }
  }
  lazy val functionSignature = P("function" ~ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ)
  lazy val formalArgList: P[Seq[PFormalArgDecl]] = P(formalArg.rep(sep = ","))
  lazy val axiomDecl = P("axiom" ~ idndef ~ "{" ~ exp ~ "}" ~ ";".?).map { case (a, b) => PAxiom1(a, b) }
  lazy val fieldDecl = P("field" ~/ idndef ~ ":" ~ typ ~ ";".?).map { case (a, b) => PField(a, b) }
  lazy val functionDecl = P("function" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
    post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, c, d, e, f) => PFunction(a, b, c, d, e, f) }

  lazy val pre = P("requires" ~/ exp ~ ";".?)
  lazy val post = P("ensures" ~/ exp ~ ";".?)

  lazy val predicateDecl = P("predicate" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ("{" ~ exp ~ "}").?).map { case (a, b, c) => PPredicate(a, b, c) }
  lazy val methodDecl = P(methodSignature ~/ pre.rep ~ post.rep ~ block.?).map {
    case (name, args, rets, pres, posts, Some(body)) =>
      PMethod(name, args, rets.getOrElse(Nil), pres, posts, PSeqn(body))
    case (name, args, rets, pres, posts, None) =>
      PMethod(name, args, rets.getOrElse(Nil), pres, posts, PSeqn(Seq(PInhale(PBoolLit(b = false)))))
  }
  lazy val methodSignature = P("method" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ("returns" ~ "(" ~ formalArgList ~ ")").?)
  lazy val fastparser = P( Start ~ programDecl ~ End)


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
  println(fastparser.parse("field next: Ref\n\nmethod Bug(nodes: Seq[Ref]) returns ()\n  requires  1 < |nodes| && !(null in nodes)\n  requires forall i: Int :: i in [0..|nodes|) ==> acc(nodes[i].next)\n  \n{\n  assert nodes[0].next == nodes[1]\n}"))
//  println(exp.parse("[0..|nodes|)"))
}
}
