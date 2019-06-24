package viper.silver.plugin

import viper.silver.parser.FastParser._
import viper.silver.plugin.trialplugin.{White, dfapp, doubleFunctionDecl}

class ParserPluginTemplate {
  /**
    * The import statements that instantiate the PWhiteSpaceApi class and then import the overloaded sequencing operators
    * of the "fastparse" library. It is extremely essential for these statements to exist in the parser.
    */
  val White = PWrapper {
    import fastparse.all._
    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }
  import White._
  import fastparse.noApi._

  /**
    * The following three 3 variables form the main three hooks for extending the parser
    */
  /**
    * The high level declarations which provide a hook for any type of independent declarations like new function or new predicates etc.
    *
    */
  lazy val newDecl = P("newExampleDeclaration")

  /**
    * The newStmt parser wich is essentially an extension of the stmt rules in the new parser.
    */
  lazy val newStmt = P("newExampleStmt")
  /**
    * THe newExp rule provides an extension to the expression parsers.
    */
  lazy val newExp = P("newExampleExpression")
}