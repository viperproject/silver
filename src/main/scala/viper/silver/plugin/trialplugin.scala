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


  lazy val functionDecl2: noApi.P[PFunction] = P("function" ~/ (functionDeclWithArg | functionDeclNoArg))

    lazy val functionDeclWithArg: noApi.P[PFunction] = P(idndef ~ "(" ~ formalArgList ~ ")" ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
            post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, g, c, d, e, f) => PFunction(a, b, c, d, e, f) }
    lazy val functionDeclNoArg: noApi.P[PFunction] = P(idndef ~ ":" ~ typ ~ pre.rep ~
      post.rep ~ ("{" ~ exp ~ "}").?).map { case (a,  c, d, e, f) => PFunction(a, Seq[PFormalArgDecl](), c, d, e, f) }


    lazy val doubleFunctionDecl: noApi.P[PDoubleFunction] = P(keyword("dfunction") ~/ idndef ~ "(" ~ formalArgList ~ ")"~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
      post.rep ~ ("{" ~ exp ~ "}").?).map{case (a, b, c, d, e, f, g) => PDoubleFunction(a, b, c, d, e, f, g)}

    lazy val newDecl = P(doubleFunctionDecl)
    lazy val newExp = P(integer)

    lazy val extendedKeywords = Set[String]("dfunction")


}
