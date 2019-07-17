
package viper.silver.parser

import viper.silver.parser.FastParser._
import viper.silver.plugin._

import scala.collection.Set

object ParserExtension extends ParserPluginTemplate {
  override val White = PWrapper {
    import fastparse.all._
    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }

  import White._
  import fastparse.noApi._


  /**
    * For more details regarding the functionality of each of these initial parser extensions
    * and other hooks for the parser extension, please refer to ParserPluginTemplate.scala
    */

  override lazy val newDeclAtEnd = P(FlowsPlugin.newDeclAtEnd | trialplugin.newDeclAtEnd)

  override lazy val newStmtAtEnd = P(trialplugin.newStmtAtEnd)

  override lazy val newExpAtEnd = P(FlowsPlugin.newExpAtEnd | trialplugin.newExpAtEnd)

  override lazy val postSpecification = P(trialplugin.postSpecification)

  override lazy val extendedKeywords = Set("flowDomain", "fdidentity", "fdplus", "DFCall", "fdi") | FlowsPlugin.extendedKeywords | trialplugin.extendedKeywords
}