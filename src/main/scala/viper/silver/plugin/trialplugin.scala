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



    lazy val functionDecl2: noApi.P[PFunction] = P("function" ~/ (functionDeclWithArg | functionDeclNoArg))

    lazy val functionDeclWithArg: noApi.P[PFunction] = P(idndef ~ "(" ~ formalArgList ~ ")" ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
            post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, g, c, d, e, f) => PFunction(a, b, c, d, e, f) }
    lazy val functionDeclNoArg: noApi.P[PFunction] = P(idndef ~ ":" ~ typ ~ pre.rep ~
      post.rep ~ ("{" ~ exp ~ "}").?).map { case (a,  c, d, e, f) => PFunction(a, Seq[PFormalArgDecl](), c, d, e, f) }


//    lazy val atom: noApi.P[PExp] = FastParser.P(integer | booltrue | boolfalse | nul | old
//      | result | unExp
//      | "(" ~ exp ~ ")" | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | applying
//      | setTypedEmpty | explicitSetNonEmpty | multiSetTypedEmpty | explicitMultisetNonEmpty | seqTypedEmpty
//      | seqLength | explicitSeqNonEmpty | seqRange | fapp | typedFapp | idnuse)

//    lazy val parseplugin = P(functionDecl | atom)

    lazy val newDecl = P(functionDecl2)
    lazy val newExp = P(integer)

    lazy val extendedKeywords = Set[String]()
}
