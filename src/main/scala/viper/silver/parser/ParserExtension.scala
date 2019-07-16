
package viper.silver.plugin

import fastparse.noApi
import viper.silver.parser.FastParser._
import viper.silver.parser._

import scala.collection.Set

object ParserExtension{
  val White = PWrapper {
    import fastparse.all._
    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }
  import White._
  import fastparse.noApi._

  lazy val newDeclAtStart: noApi.P[PExtender] = null
  lazy val newStmtAtStart: noApi.P[PStmt] = null
  lazy val newDeclAtEnd = P(FlowsPlugin.flowDomain)
  lazy val  newStmtAtEnd: noApi.P[PStmt] = null
  lazy val newExpAtEnd = P(FlowsPlugin.flowDomainCall | FlowsPlugin.flowDomainIdenUse)
  lazy val newExpAtStart: noApi.P[PExp] = null
  lazy val preSpecification: noApi.P[PExp] = P("preConditionSpecificationExample").map{case() => "".asInstanceOf[PExp]}
  lazy val postSpecification: noApi.P[PExp] = P("postConditionSpecificationExample").map{case() => "".asInstanceOf[PExp]}
  lazy val invSpecification: noApi.P[PExp] = P("invariantSpecificationExample").map{case() => "".asInstanceOf[PExp]}

  lazy val extendedKeywords = Set("flowDomain", "fdidentity", "fdplus", "DFCall", "fdi")
}