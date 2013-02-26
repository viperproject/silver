package semper.sil.parser

import org.kiama.util.PositionedParserUtilities

/**
 * A parser for the SIL language that takes a string and produces an intermediate
 * AST ([[semper.sil.parser.PNode]]), or a parse error.  The intermediate AST can
 * then be type-checked and translated into the SIL AST ([[semper.sil.ast.Node]])
 * using [[semper.sil.parser.Translator]].
 */
object Parser extends BaseParser {
  def parse(s: String) = {
    val r = parseAll(parser, s)
    r match {
      // make sure the tree is correctly initialized
      case Success(e, _) => e.initTreeProperties()
      case _ =>
    }
    r
  }
}

trait BaseParser extends PositionedParserUtilities {

  /** All keywords of SIL. */
  def reserved: List[String] = List(
    // special variables
    "this", "result",
    // types
    "Int", "Perm", "Bool", "Ref",
    // boolean constants
    "true", "false",
    // declaration keywords
    "method", "function", "predicate", "program", "domain", "axiom",
    // specifications
    "requires", "ensures", "old", "invariants",
    // statements
    "fold", "unfold", "inhale", "exhale",
    // control structures
    "while", "if", "else",
    // special fresh block
    "fresh"
  )

  lazy val parser = phrase(methodDecl)

  // --- Declarations

  lazy val methodDecl =
    methodSignature ~ rep(pre) ~ rep(post) ~ block ^^ {
      case name ~ args ~ rets ~ pres ~ posts ~ body =>
        PMethod(name, args, rets.getOrElse(Nil), pres, posts, PSeqn(body))
    }
  lazy val methodSignature =
    ("method" ~> idndef) ~ ("(" ~> formalArgList <~ ")") ~ opt("returns" ~> ("(" ~> formalArgList <~ ")"))
  lazy val pre =
    "requires" ~> exp <~ opt(";")
  lazy val post =
    "ensures" ~> exp <~ opt(";")
  lazy val inv =
    "invariant" ~> exp <~ opt(";")

  lazy val formalArgList =
    repsep(formalArg, ",")
  lazy val formalArg =
    idndef ~ (":" ~> typ) ^^ PFormalArgDecl

  // --- Statements

  def parens[A](p: Parser[A]) = "(" ~> p <~ ")"

  lazy val block: Parser[Seq[PStmt]] =
    "{" ~> (stmts <~ "}")
  lazy val stmts =
    rep(stmt <~ opt(";"))
  lazy val stmt =
    assign | fold | unfold | exhale | inhale | ifthnels | whle | varDecl

  lazy val fold =
    "fold" ~> exp ^^ PFold
  lazy val unfold =
    "unfold" ~> exp ^^ PUnfold
  lazy val inhale =
    "inhale" ~> parens(exp) ^^ PInhale
  lazy val exhale =
    "exhale" ~> parens(exp) ^^ PExhale
  lazy val assign =
    idnuse ~ (":=" ~> exp) ^^ PVarAssign
  lazy val ifthnels =
    ("if" ~> "(" ~> exp <~ ")") ~ block ~ opt("else" ~> block) ^^ {
      case cond ~ thn ~ els =>
        PIf(cond, PSeqn(thn), PSeqn(els.getOrElse(Nil)))
    }
  lazy val whle =
    ("while" ~> "(" ~> exp <~ ")") ~ rep(inv) ~ block ^^ {
      case cond ~ invs ~ body => PWhile(cond, invs, PSeqn(body))
    }
  lazy val varDecl =
    ("var" ~> idndef) ~ (":" ~> typ) ~ opt(":=" ~> exp) ^^ PLocalVarDecl
  lazy val freshReadPerm =
    ("fresh" ~> "(" ~> repsep(idnuse, ",") <~ ")") ~ block ^^ {
      case vars ~ stmts => PFreshReadPerm(vars, PSeqn(stmts))
    }

  // --- Types

  lazy val typ =
    primitiveTyp | typVar
  // TODO: | domainTyp
  lazy val primitiveTyp =
    ("Int" | "Bool" | "Perm" | "Ref") ^^ PPrimitiv
  lazy val typVar =
    ident ^^ PTypeVar

  // --- Expressions

  lazy val exp: PackratParser[PExp] =
    iffExp

  // TODO
  //lazy val iteExpr: Parser[Expression] =
  //iffExpr ~ ("?" ~> iteExpr) ~ (":" ~> iteExpr) ^^ {
  lazy val iffExp: PackratParser[PExp] =
    implExp ~ "<==>" ~ iffExp ^^ PBinExp | implExp
  lazy val implExp: PackratParser[PExp] =
    orExp ~ "==>" ~ implExp ^^ PBinExp | orExp
  lazy val orExp: PackratParser[PExp] =
    andExp ~ "||" ~ orExp ^^ PBinExp | andExp
  lazy val andExp: PackratParser[PExp] =
    cmpExp ~ "&&" ~ andExp ^^ PBinExp | cmpExp

  lazy val cmpOp = "==" | "!=" | "<" | "<=" | ">=" | ">" | "<<" | "in" | "!in"
  lazy val cmpExp: PackratParser[PExp] =
    sum ~ cmpOp ~ sum ^^ PBinExp | sum

  lazy val sum: PackratParser[PExp] =
    sum ~ "+" ~ term ^^ PBinExp |
      sum ~ "-" ~ term ^^ PBinExp |
      term

  lazy val term: PackratParser[PExp] =
    term ~ "*" ~ factor ^^ PBinExp |
      term ~ "/" ~ factor ^^ PBinExp |
      factor

  lazy val factor: PackratParser[PExp] =
    fieldAcc | integer | bool | idnuse | "result" ^^^ PResultLit() | "this" ^^^ PThisLit() |
      "-" ~ sum ^^ PUnExp | "(" ~> exp <~ ")"

  lazy val fieldAcc: PackratParser[PExp] =
    (exp <~ ".") ~ idnuse ^^ PFieldAcc

  lazy val integer =
    "[0-9]+".r ^^ (s => PIntLit(BigInt(s)))

  lazy val bool =
    "true" ^^^ PBoolLit(b = true) | "false" ^^^ PBoolLit(b = false)

  lazy val idndef =
    ident ^^ PIdnDef

  lazy val idnuse =
    ident ^^ PIdnUse

  // --- Identifier and keywords

  lazy val ident =
    not(keyword) ~> identifier.r |
      failure("identifier expected")
      
  lazy val identFirstLetter = "[a-zA-Z$_]"
    
  lazy val identOtherLetter = "[a-zA-Z0-9$_']"

  lazy val identifier = identFirstLetter + identOtherLetter + "*"

  lazy val keyword =
    keywords("[^a-zA-Z0-9]".r, reserved)
}
