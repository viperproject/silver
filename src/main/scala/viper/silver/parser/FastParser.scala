package viper.silver.parser

/**
  * Created by sahil on 24.05.16.
  */

import fastparse.parsers.Combinators.Rule
import fastparse.WhitespaceApi
import fastparse.parsers.Intrinsics






package object Main {
  def main(args: Array[String]) {
    val White = WhitespaceApi.Wrapper{
      import fastparse.all._
      NoTrace(" ".rep)
    }
    import fastparse.noApi._
//   import fastparse.all._
    import White._


    // code starts from here

    def tester(test: String) = "1"

    //from here the code starts
    def keyword(check : String) =  check ~~ !CharIn('0' to '9','A' to 'Z', 'a' to 'z')
    def parens[A](p : Parser[A]) = "(" ~ p ~ ")"
    def foldPExp[E <: PExp](e: PExp, es: Seq[PExp => E]): E =
    es.foldLeft(e){(t, a) =>
      val result = a(t)
      result.setPos(t)
      result
    }.asInstanceOf[E]

    def getFieldAccess(obj: Any) = obj match {
      case n: PFieldAccess => true
      case _ => false
    }


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
      "unique") ~~ !CharIn('0' to '9','A' to 'Z', 'a' to 'z'))

    /*



    *
    *
    *
    * */

    lazy val integer = P(CharIn('0' to '9').rep(1)).!.map{s => PIntLit(BigInt(s)) }
    lazy val booltrue = P(keyword("true")).map(_ => PBoolLit(b = true))
    lazy val boolfalse = P(keyword("false")).map(_ => PBoolLit(b = false))
    lazy val nul = P(keyword("null")).map( _ => PNullLit())

    lazy val identifier = P(CharIn('A' to 'Z', 'a' to 'z',"$_") ~~ CharIn('0' to '9' , 'A' to 'Z', 'a' to 'z',"$_").repX)
    lazy val ident = P(!iskey ~ identifier.rep.!  )
    //possible customize error code in rule ident
    lazy val idnuse: P[PIdnUse] = P(ident ).map(PIdnUse)

    lazy val old: P[PExp] = P((StringIn("old") ~/ parens(exp)).map(POld) | ("[" ~ idnuse ~ "]" ~ parens(exp)).map{case(a,b) => PLabelledOld(a,b)} )
    lazy val applyOld: P[PExp] =P((StringIn("lhs") ~/ parens(exp)).map(PApplyOld) )








    lazy val atom: P[PExp] = P(integer| booltrue| boolfalse| nul| old| applyOld
      | keyword("result").map{_ => PResultLit()} |  (CharIn("-!+").! ~ sum).map{case(a,b) => PUnExp(a,b)}
      | "(" ~/ exp ~ ")" | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | folding | applying
      | packaging | setTypedEmpty | explicitSetNonEmpty | explicitMultisetNonEmpty


    )














    lazy val magicWandExp:P[PExp] = P(realMagicWandExp | orExp)
    lazy val realMagicWandExp:P[PExp] = P((orExp ~ "--*".! ~ magicWandExp).map{case(a,b,c) =>  PBinExp(a,b,c)})
    lazy val implExp: P[PExp] = P((magicWandExp ~ "==>".! ~ implExp).map{case(a,b,c) =>  PBinExp(a,b,c)} | magicWandExp)
    lazy val iffExp: P[PExp] = P((implExp ~ "<==>".! ~ iffExp).map{case(a,b,c) =>  PBinExp(a,b,c)} | implExp)
    lazy val iteExpr:P[PExp] = P((iffExp ~ "?" ~ iteExpr ~ ":" ~ iteExpr).map{case(a,b,c) =>  PCondExp(a,b,c)} | iffExp)
    lazy val exp: P[PExp] =  P(iteExpr)

    lazy val suffix: Parser[PExp => PExp] =
      P(("." ~ idnuse).map{id => (e: PExp) => PFieldAccess(e, id)} |
        ("[.." ~ exp ~ "]").map{n => (e: PExp) => PSeqTake(e, n)} |
        ("[" ~ exp ~ "..]").map{n => (e: PExp) => PSeqDrop(e, n)} |
        ("[" ~ exp ~ ".." ~ exp ~ "]" ).map{case( n , m )=> (e: PExp) => PSeqDrop(PSeqTake(e, m), n)} |
        ("[" ~ exp ~ "]").map{e1 => (e0: PExp) => PSeqIndex(e0, e1)} |
        ("[" ~ exp ~ ":=" ~ exp ~ "]").map{case( i, v) => (e: PExp) => PSeqUpdate(e, i, v)})

    lazy val suffixExpr: P[PExp] =P((atom ~ suffix.rep).map{case (fac, ss) => foldPExp[PExp](fac, ss)})

    lazy val realSuffixExpr: P[PExp] =P((atom ~ (suffix).rep).map{case (fac, ss) => foldPExp[PExp](fac, ss)})

    lazy val termOp = P(StringIn("*" , "/" , "\\" , "%").!)
    lazy val term: P[PExp] = P((suffixExpr ~ termd.rep).map{ case (a, ss)  => foldPExp[PExp](a, ss)})
    lazy val termd: P[PExp => PBinExp] =P(termOp ~ suffixExpr).map{ case(op, id ) => (e: PExp) => PBinExp(e, op , id) }
    lazy val sumOp = P(StringIn("++" ,"+" ,"-" ).! | keyword("union").! | keyword("intersection").! |   keyword("setminus").! |  keyword("subset").!)
    lazy val sum: P[PExp] =P((term ~ sumd.rep).map{case(a, ss) =>  foldPExp[PBinExp](a,ss)})
    lazy val sumd: P[PExp => PBinExp] =P(sumOp ~ term).map{ case(op , id) => (e: PExp) => PBinExp(e,op,id) }
    lazy val cmpOp = P(StringIn("<=", ">=" , "<", ">").! | keyword("in").!)
    lazy val cmpExp: P[PExp] =P((sum ~ cmpOp ~ cmpExp).map{case(a,b,c) => PBinExp(a,b,c)}  | sum)

    lazy val eqOp = P(StringIn("==" ,"!=").!)
    lazy val eqExp:P[PExp] =  P((cmpExp ~ eqOp ~ eqExp).map{case(a,b,c) => PBinExp(a,b,c)} | cmpExp)
    lazy val andExp:P[PExp] = P((eqExp ~ "&&".! ~ andExp).map{case(a,b,c) =>  PBinExp(a,b,c)} | eqExp)
    lazy val orExp:P[PExp] = P((andExp ~ "||".! ~ orExp).map{case(a,b,c) =>  PBinExp(a,b,c)} | andExp )

    lazy val accessPred: P[PAccPred] = P(StringIn("acc") ~/ parens(locAcc ~ ("," ~ exp).?).map{case (loc , perms) => PAccPred(loc, perms.getOrElse(PFullPerm()))})
    lazy val locAcc: P[PLocationAccess] =P(fieldAcc | predAcc)
    //this rule is in doubt :D
    lazy val fieldAcc :P[PFieldAccess] = P(realSuffixExpr.filter(getFieldAccess).map{case fa: PFieldAccess => fa}).opaque("Field Expected")
    lazy val predAcc: P[PPredicateAccess] = P(idnuse ~ parens(actualArgList)).map{case (id,args) => PPredicateAccess(args, id)}
    //is it required to be one or more than 1 below
    lazy val actualArgList: P[Seq[PExp]] =  P(exp).rep(sep = ",")
    lazy val inhaleExhale: P[PExp] = P("[" ~ exp ~ "," ~ exp ~ "]").map{case(a,b) => PInhaleExhaleExp(a,b)}
    lazy val perm: P[PExp] =P(keyword("none").map(_ => PNoPerm()) | keyword("wildcard").map(_ => PWildcard()) | keyword("write").map(_ => PFullPerm())
                            |keyword("epsilon").map(_ => PEpsilon()) | ("perm" ~ parens(locAcc)).map(PCurPerm))
  //doubt (how is this working!!!! - Uses KIama Stuff :( )
    lazy val let: P[PExp] = P(
      ("let" ~ idndef ~ "==" ~ "(" ~ exp ~ ")" ~ "in" ~ exp).map{ case (id , exp1 , exp2) =>
        /* Type unresolvedType is expected to be replaced with the type of exp1
         * after the latter has been resolved
         * */
        val unresolvedType = PUnknown().setPos(id)
        val formalArgDecl = PFormalArgDecl(id, unresolvedType).setPos(id)
        val nestedScope = PLetNestedScope(formalArgDecl, exp2).setPos(exp2)

        PLet(exp1, nestedScope)
      })
    lazy val idndef = P(ident).map(PIdnDef)

    lazy val quant: P[PExp] =P((keyword("forall") ~ nonEmptyFormalArgList ~ "::" ~ trigger.rep ~ exp).map{case(a,b,c) => PForall(a,b,c)} |
                               (keyword("exists") ~ nonEmptyFormalArgList ~ "::" ~ exp).map{case(a,b) => PExists(a,b)})
    lazy val nonEmptyFormalArgList: P[Seq[PFormalArgDecl]] = P(formalArg.rep(sep = ","))
    lazy val formalArg: P[PFormalArgDecl] =P(idndef ~ ":" ~ typ).map{case(a,b) => PFormalArgDecl(a,b)}
    //types
    lazy val typ: P[PType] = P( primitiveTyp | domainTyp | seqType | setType | multisetType)
    lazy val domainTyp: P[PDomainType] = P((idnuse ~ "[" ~ typ.rep(sep = ",") ~ "]").map{case(a,b) => PDomainType(a,b)} |
                        idnuse.map{// domain type without type arguments (might also be a type variable)
                          case name => PDomainType(name, Nil)
                        })
    lazy val seqType: P[PType] =P("Seq" ~ "[" ~ typ ~ "]").map(PSeqType)
    lazy val setType: P[PType] = P("Set" ~ "[" ~ typ ~ "]").map(PSetType)
    lazy val multisetType: P[PType] = P("Multiset" ~ "[" ~ typ ~ "]").map(PMultisetType)
    lazy val primitiveTyp: P[PType] = P(StringIn("Rational")).!.map{ case _ => PPrimitiv("Perm") } | StringIn("Int","Bool","Perm","Ref").!.map(PPrimitiv)
    lazy val trigger: P[Seq[PExp]] = P("{" ~ exp.rep(sep = ",") ~ "}")
    //showing red but possibly correct checked on forperm [ ] hello::2*2
    lazy val forperm: P[PExp] =P( keyword("forperm") ~ "[" ~ idnuse.rep(sep = ",") ~ "]" ~ idndef ~ "::" ~ exp).map{
                                case (ids , id ,body) => PForPerm(PFormalArgDecl(id, PPrimitiv("Ref")), ids, body)
                              }
    lazy val unfolding: P[PExp] = P("unfolding" ~ predicateAccessPred ~ "in" ~ exp).map{case(a,b) => PUnfolding(a,b)}
    lazy val predicateAccessPred: P[PAccPred] = P(accessPred | predAcc.map{case loc => PAccPred(loc, PFullPerm())})
    lazy val folding: P[PExp] =P ("folding" ~ predicateAccessPred ~ "in" ~ exp).map{case(a,b) => PFoldingGhostOp(a,b)}

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
      P((("applying" ~ "(" ~ realMagicWandExp ~ ")" )| idnuse) ~ "in" ~ exp).map{case(a,b) => PApplyingGhostOp(a,b)}

    lazy val packaging: P[PExp] = /* See comment on applying */
      P("packaging" ~ ("(" ~ realMagicWandExp ~ ")" | idnuse) ~ "in" ~ exp).map{case(a,b) => PPackagingGhostOp(a,b)}
    lazy val setTypedEmpty: P[PExp] =  P("Set" ~ "[" ~ typ ~ "]" ~ "(" ~ ")").map{case a => PEmptySet(a)}
    lazy val explicitSetNonEmpty: P[PExp] = P( "Set" /*~ opt("[" ~> typ <~ "]")*/ ~ "(" ~ exp.rep(sep = ",") ~ ")").map(PExplicitSet)
    lazy val explicitMultisetNonEmpty: P[PExp] = P("Multiset" ~ "(" ~ exp.rep(min = 1, sep= ",") ~ ")").map{case elems => PExplicitMultiset(elems)}






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

    println(forperm.parse("forperm [ ] hello::2*2"))









  }

}
