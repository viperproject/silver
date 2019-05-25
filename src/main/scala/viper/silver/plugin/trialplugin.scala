package viper.silver.plugin

import viper.silver.parser.FastParser._
//import viper.silver.parser.PosParser[Char, String]._
import fastparse.all._
import fastparse.noApi.P
import viper.silver.parser.{PFormalArgDecl, PFunction}

object trialplugin extends SilverPlugin{

    val functionDecl2: P[PFunction] = P(keyword("function") ~/ idndef ~  ":" ~ typ ~ pre.rep ~
    post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, c, d, e, f) => PFunction(a, Seq[PFormalArgDecl](), c, d, e, f) }.log()

    lazy val pluginTest: P[PFunction] = P(keyword("pluginTest") )
}
