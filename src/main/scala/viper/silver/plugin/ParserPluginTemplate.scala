package viper.silver.plugin

import viper.silver.parser.{NameAnalyser, PExp, PExtender, PStmt, PTypeSubstitution, Translator, TypeChecker}
import fastparse.noApi
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.{Declaration, ErrorTrafo, ExtMember, ExtensionExp, ExtensionStmt, Info, Node, Position, Type}
import viper.silver.parser.FastParser._
import viper.silver.verifier.VerificationResult

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
  lazy val newDecl: noApi.P[PExtender] = P("PExampleDeclaration").map {case() => PExampleDeclaration()}
  /**
    * The newStmt parser wich is essentially an extension of the stmt rules in the new parser.
    */
  lazy val newStmt: noApi.P[PStmt] = P("PExampleStmt").map {case () => PExampleStmt()}
  /**
    * The newExp rule provides an extension to the expression parsers.
    */
  lazy val newExp: noApi.P[PExp] = P("PExampleExpression").map {case() => PExampleExp()}

  /**
    * The specification rule provides an extension to the precondition expressions
    */
  lazy val preSpecification: noApi.P[PExp] = P("preconditionSpecificationExample").map{case() => "".asInstanceOf[PExp]}
  /**
    * The specification rule provides an extension to the postcondition expressions
    */
  lazy val postSpecification: noApi.P[PExp] = P("postconditionSpecificationExample").map{case() => "".asInstanceOf[PExp]}
  /**
    * The specification rule provides an extension to the loop invariant specification expressions
    */
  lazy val invSpecification: noApi.P[PExp] = P("invariantSpecificationExample").map{case() => "".asInstanceOf[PExp]}

  case class PExampleDeclaration() extends PExtender{
    // The typechecker for this PAst node
    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = ???
    // These two founction for translating PAst to Ast nodes are applicable only in the case of this class being a high level declaration
    override def translateMem(t: Translator): ExtMember = ???
    override def translateMemSignature(t: Translator): ExtMember = super.translateMemSignature(t)
  }

  case class PExampleStmt() extends PExtender with PStmt{
    //The overridden typechecker for this PAst node
    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = ???
    
    // The overridden function to translate this node to a corresponding Ast node
    override def translateStmt(t: Translator): ExtensionStmt = super.translateStmt(t)
  }

  case class PExampleExp() extends PExtender with PExp{
    // These two function must be mandatorily extended due to semantic analysis rules
    override def typeSubstitutions: Seq[PTypeSubstitution] = ???
    override def forceSubstitution(ts: PTypeSubstitution): Unit = ???
    
    // The typecheck funtion for PAst node corresponding to the expression
    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = super.typecheck(t, n)
    // The translator function to translate the PAst node corresponding to the Ast node
    override def translateExp(t: Translator): ExtensionExp = super.translateExp(t)
  }

  /**
    * The Ast Class for the high level declarations
    * These must inherit the viper.silver.ast.ExtMember class
    */
  case class ExampleDeclaration() extends ExtMember{
    // All these are necessary methods for class inheritence
    override def pos: Position = ???
    override val scopedDecls: Seq[Declaration] = Seq()
    override def extensionsubnodes: Seq[Node] = ???
    override def name: String = ???
    override def errT: ErrorTrafo = ???
    override def info: Info = ???
  }

  /**
    * The Ast Class for the statements
    * These must inherit the viper.silver.ast.ExtensionStmt class
    */
  case class ExampleStmt() extends ExtensionStmt{
    // All these are necessary methods for class inheritence
    override def pos: Position = ???
    override def extensionSubnodes: Seq[Node] = ???
    override def errT: ErrorTrafo = ???
    override def info: Info = ???
    override def prettyPrint: PrettyPrintPrimitives#Cont = ???
  }

  /**
    * The Ast Class for the expressions
    * These must inherit the viper.silver.ast.ExtensionExp class
    */
  case class ExampleExp() extends  ExtensionExp{
    override def errT: ErrorTrafo = ???
    override def info: Info = ???
    override def pos: Position = ???
    override def typ: Type = ???
    override def extensionIsPure: Boolean = ???
    override def extensionSubnodes: Seq[Node] = Seq()
    override def prettyPrint: PrettyPrintPrimitives#Cont = ???

    /**
    * This function is used to verify custom expressions.
    * This function's usage has not at all been tested and hence
    * @return viper.silver.verifier.VerificationResult
    */
    override def verifyExtExp(): VerificationResult = ???
  }



}