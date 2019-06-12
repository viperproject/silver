package viper.silver.plugin

//import fastparse.all._
//import
import fastparse.noApi
import viper.silver.parser.FastParser._
import viper.silver.parser.PosParser
import viper.silver.parser.{PFunction, _}



object trialplugin  extends PosParser[Char, String] {




    val White = PWrapper {
        import fastparse.all._
        NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
    }
    import White._
    import fastparse.noApi._

  case class PDoubleFunction( idndef: PIdnDef,  formalArgs: Seq[PFormalArgDecl], formalArgsSecondary: Seq[PFormalArgDecl],  rettyp: PType,  pres: Seq[PExp], posts: Seq[PExp], body: Option[PExp]) extends PExtender {
    override def getsubnodes(): Seq[PNode] ={
      Seq(this.idndef) ++ this.formalArgs ++ this.formalArgsSecondary ++ Seq(this.rettyp) ++ this.pres ++ this.posts ++ this.body
    }
  }

  case class PStrDef(idndef: PIdnDef, value: String) extends PExp with PExtender {
    override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

    override def typeSubstitutions: Seq[PTypeSubstitution] = ???
  }

  case class PDoubleCall(dfunc: PIdnUse, argList1: Seq[PExp], argList2: Seq[PExp]) extends PExtender with PExp{
    override def typeSubstitutions: Seq[PTypeSubstitution] = ???

    override def forceSubstitution(ts: PTypeSubstitution): Unit = ???
  }


  lazy val functionDecl2: noApi.P[PFunction] = P("function" ~/ (functionDeclWithArg | functionDeclNoArg))

    lazy val functionDeclWithArg: noApi.P[PFunction] = P(idndef ~ "(" ~ formalArgList ~ ")" ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
            post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, g, c, d, e, f) => PFunction(a, b, c, d, e, f) }
    lazy val functionDeclNoArg: noApi.P[PFunction] = P(idndef ~ ":" ~ typ ~ pre.rep ~
      post.rep ~ ("{" ~ exp ~ "}").?).map { case (a,  c, d, e, f) => PFunction(a, Seq[PFormalArgDecl](), c, d, e, f) }


    lazy val doubleFunctionDecl: noApi.P[PDoubleFunction] = P(keyword("dfunction") ~/ idndef ~ "(" ~ formalArgList ~ ")"~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
      post.rep ~ ("{" ~ exp ~ "}").?).map{case (a, b, c, d, e, f, g) => PDoubleFunction(a, b, c, d, e, f, g)}

    lazy val stringtyp: noApi.P[PType] = P("String" ~~ !identContinues).!.map(PPrimitiv)

    lazy val newDecl = P(doubleFunctionDecl)

// String var_name := "afasfsdaf"
    lazy val stringDef: noApi.P[PStrDef] = P(stringtyp ~/ idndef ~ ":=" ~ "\"" ~ (AnyChar.rep).! ~ "\"").map{case(_, b,c) => PStrDef(b, c)}

    lazy val dfapp: noApi.P[PDoubleCall] = P(idnuse ~ parens(actualArgList) ~ parens(actualArgList)).map {case (a,b,c) => PDoubleCall(a,b,c)}.log()

    // This newExp extension is not yet used
    lazy val newExp = P(stringDef | dfapp).log()
    lazy val newStmt = P(block)

    lazy val extendedKeywords = Set[String]("dfunction")


}
