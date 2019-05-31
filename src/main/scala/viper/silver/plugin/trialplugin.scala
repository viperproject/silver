package viper.silver.plugin

import java.nio.file.Path

import viper.silver.parser.FastParser.PWrapper

//import fastparse.all._
import fastparse.core.Implicits.{Repeater, Sequencer}
import fastparse.core.Parser
import fastparse.utils.ReprOps
//import
import fastparse.{WhitespaceApi, all, noApi}
import viper.silver.parser.FastParser.{idndef, formalArgList, typ, pre, post, exp}
import viper.silver.parser.PosParser
//import viper.silver.parser.PosParser.PWhitespaceApi
import viper.silver.parser.{PExp, PFunction, _}
//import White.parserApi
//import White._


object trialplugin  extends PosParser[Char, String] {

//    val tmp = new PWhitespaceApi[PIdnDecl]
//    import tmp._


    val White = PWrapper {
        import fastparse.all._
        NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
    }
    import fastparse.noApi._
    import White._



    lazy val functionDecl: noApi.P[PFunction] = P("function" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
      post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, c, d, e, f) => PFunction(a, b, c, d, e, f) }


//    lazy val atom: noApi.P[PExp] = FastParser.P(integer | booltrue | boolfalse | nul | old
//      | result | unExp
//      | "(" ~ exp ~ ")" | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | applying
//      | setTypedEmpty | explicitSetNonEmpty | multiSetTypedEmpty | explicitMultisetNonEmpty | seqTypedEmpty
//      | seqLength | explicitSeqNonEmpty | seqRange | fapp | typedFapp | idnuse)
}
