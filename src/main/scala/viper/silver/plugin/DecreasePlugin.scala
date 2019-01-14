
package viper.silver.plugin

import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, show, space, ssep, text, toParenDoc}
import viper.silver.parser._
import viper.silver.verifier.{Failure, Success, VerificationResult}


// run --printTranslatedProgram --plugin viper.silver.plugin.DecreasePlugin silver/src/test/resources/termination/basic/test.vpr
class DecreasePlugin extends SilverPlugin
{

  // decreases "keyword"
  private val DECREASES = "decreases"

  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeResolve(input: PProgram): PProgram = {
    // replace all decreases (calls in postconditions)
    // with decreasesN calls
    // and add DecreasesDomain with all needed decreasesN functions

    var newFunctions = Seq[PFunction]()

    for(function <- input.functions){
      var posts = Seq[PExp]()

      for(post <- function.posts){
        post match {
          case call: PCall =>
            if (call.opName == DECREASES) {
              // change call
              val argsSize = call.args.length
              val functionName = getDecreasesNFunction(argsSize)
              posts = posts :+ call.copy(func = PIdnUse(functionName))
            } else {
              posts = posts :+ post
            }
          case _ =>
            posts = posts :+ post
        }
      }
      newFunctions = newFunctions :+ function.copy(posts = posts)
    }

    val newDomain = createDecreasesDomain(getDecreasesNDomain, decreasesNFunctions.toMap)

    input.copy(functions = newFunctions, domains = input.domains :+ newDomain)
  }

  /**
    * All needed decreasesN functions
    * (#arguments -> function name)
    */
  private val decreasesNFunctions = collection.mutable.Map[Integer, String]()

  /**
    * Lazy map using the decreasesNFunctions
    * @param argsSize: number of arguments needed
    * @return name of decrease function
    */
  private def getDecreasesNFunction(argsSize: Integer): String = {
    if (!decreasesNFunctions.contains(argsSize)){
      val newName: String = s"$$decreases${argsSize}"
      decreasesNFunctions += (argsSize -> newName)
    }
    decreasesNFunctions(argsSize)
  }

  private def getDecreasesNDomain: String ={
    "$DecreasesDomain"
  }

  /**
    * Creates a DecreasesDomain with type parameters
    * @param domain name of the created domain
    * @param functions #arguments -> function name
    * @return the DecreasesDomain
    */
  private def createDecreasesDomain(domain: String, functions: Map[Integer, String]): PDomain = {

    val domainIdDef = PIdnDef(domain)
    val domainIdUse = PIdnUse(domain)

    // number of type parameters needed
    val maxArgs: Integer = functions.keySet.max

    // all type parameters
    val typeVars = Seq.tabulate(maxArgs)(i => PTypeVarDecl(PIdnDef(s"T$i")))

    // list of arguments with the type parameter
    val formalArgs: Seq[PFormalArgDecl] = typeVars.map(t => PFormalArgDecl(PIdnDef(s"v${t.idndef.name}"), PDomainType(PIdnUse(t.idndef.name), Seq())))

    // all needed decreasesN functions
    val decreasesFunctions = functions.map {
      case (argsSize, functionName) => {
        PDomainFunction(PIdnDef(functionName), formalArgs.take(argsSize), PPrimitiv(TypeHelper.Bool.name), false)(domainIdUse)
      }
    }(collection.breakOut)

    PDomain(domainIdDef, typeVars, decreasesFunctions, Seq())
  }

  /** Called after parse AST has been translated into the normal AST but before methods to verify are filtered.
    * In [[viper.silver.frontend.SilFrontend]] this step is confusingly called doTranslate.
    *
    * @param input AST
    * @return Modified AST
    */
  override def beforeMethodFilter(input: Program): Program = {
    // get all decreases in post conditions and
    // transform them to one post condition with a DecreaseExp
    // replace decreasesN again with decreases
    var newFunctions = Seq[Function]()
    val decreasesN = decreasesNFunctions.values.toSeq

    for (function <- input.functions){
      val posts = function.posts map {
        case c: Call => {
          if (decreasesNFunctions.get(c.args.size).contains(c.callee)) {
            DecreaseExp(true, c.pos, c.args)
          }else {
            c
          }
        }
        case p => p
      }
      newFunctions = newFunctions :+ function.copy(posts = posts)(function.pos, function.info, function.errT)
    }

    val newDomains = input.domains.filterNot(d => d.name == getDecreasesNDomain)

    // copy the program with the new functions
    input.copy(functions = newFunctions, domains = newDomains)(input.pos, input.info, input.errT)
  }

  /** Called after methods are filtered but before the verification by the backend happens.
    *
    * @param input AST
    * @return Modified AST
    */
  override def beforeVerify(input: Program): Program = {

    // remove all post conditions which are DecreaseExp
    // and add them to the functions -> decreases map
    var newFunctions = Seq[Function]()
    val decreaseMap = scala.collection.mutable.Map[Function, DecreaseExp]()

    for (function <- input.functions) {
      var decreaseClause: DecreaseExp = null
      var posts = Seq[Exp]()

      for (post <- function.posts) {
        if (post.isInstanceOf[DecreaseExp]) {
          // add to the decrease map
          decreaseClause = post.asInstanceOf[DecreaseExp]
        }else{
          posts = posts :+ post
        }
      }

      val newFunction = function.copy(posts = posts)(function.pos, function.info, function.errT)
      newFunctions = newFunctions :+ newFunction

      if (decreaseClause != null){
        decreaseMap += (newFunction -> decreaseClause)
      }
    }

    // new program without any DecreaseExp
    val newProgram: Program = input.copy(domains = input.domains, functions = newFunctions, methods = input.methods)(input.pos, input.info, input.errT)


    val locDom = newProgram.domains.find(d => d.name.equals("Loc"))
    val decFunc = newProgram.findDomainFunctionOptionally("decreasing")
    val boundFunc = newProgram.findDomainFunctionOptionally("bounded")
    val nestFunc = newProgram.findDomainFunctionOptionally("nested")

    val termCheck = new DecreasesClause2(newProgram, decreaseMap.toMap)
    val structureForTermProofs = termCheck.addMethods(newProgram.functions, newProgram.predicates, newProgram.domains, decFunc, boundFunc, nestFunc, locDom)

    val d = structureForTermProofs._1
    val f = structureForTermProofs._2
    val m = structureForTermProofs._3

    newProgram.copy(domains = d, functions = newProgram.functions ++ f, methods = newProgram.methods ++ m)(newProgram.pos, newProgram.info, newProgram.errT)
  }
}

case class DecreaseExp(extensionIsPure: Boolean, pos: Position, extensionSubnodes: Seq[Exp]) extends ExtensionExp {

  override def typ: Type = Bool

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */

  override def info: Info = NoInfo

  override def errT: ErrorTrafo = NoTrafos

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = text("decreases") <> parens(ssep(extensionSubnodes map (toParenDoc(_)), char(',') <> space))




  /**
    * Method that accesses all children of a node.
    * We allow 3 different types of children: Rewritable, Seq[Rewritable] and Option[Rewritable]
    * The supertype of all 3 is AnyRef
    *
    * @return Sequence of children
    */
  override def getChildren: Seq[Exp] = extensionSubnodes

  override def duplicate(children: Seq[AnyRef]): DecreaseExp = {
    children match {
      case Seq(args: List[Exp]) => DecreaseExp(extensionIsPure, pos, args)
    }
  }
}
