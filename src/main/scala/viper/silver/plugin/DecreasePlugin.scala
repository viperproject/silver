
package viper.silver.plugin

import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, show, space, ssep, text, toParenDoc}
import viper.silver.parser._


// run --printTranslatedProgram --plugin viper.silver.plugin.DecreasePlugin silver/src/test/resources/termination/basic/test.vpr
class DecreasePlugin extends SilverPlugin
{

  /*

  /** Called before any processing happened.
    *
    * @param input      Source code as read from file
    * @param isImported Whether the current input is an imported file or the main file
    * @return Modified source code
    */
  override def beforeParse(input: String, isImported: Boolean): String = {
    if (!isImported){
      "domain DecreaseDomain[T]{function decreases(t: T):Bool}\n" + input
    }else{
      input
    }
  }
  */



  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeResolve(input: PProgram): PProgram = {
    // get the arguments of all decreases calls in postconditions
    // and remove them
    println("old:")
    println(input)


    val decreaseDomain = input.domains.find(d => d.idndef.name == "DecreaseDomainx").get

    var newFunctions = Seq[PFunction]()

    for(function <- input.functions){
      var posts = Seq[PExp]()
      var args: Seq[PExp] = null;

      for(post <- function.posts){
        if (post.isInstanceOf[PCall]){
          val call = post.asInstanceOf[PCall]
          if (call.opName == "decreases"){
            // remove post condition and store it
            val argsSize = call.args.length

            val decreaseN = getDecreaseN(decreaseDomain, argsSize)

            //posts = posts :+ post

          }else{
            posts = posts :+ post
          }
        }else{
          posts = posts :+ post
        }
      }
      val newFunction = function.copy(posts = posts)
      newFunctions = newFunctions :+ function.copy(posts = posts)
    }


    val newDomains: Seq[PDomain] = decreaseNFunctions.values.toSeq

    val newProgram = input.copy(functions = newFunctions, domains = newDomains)


    println("New Program:")
    println(newProgram.functions)
    println(newProgram.domains)
    newProgram
  }

  // #arguments -> (domain name, function name)
  val decreaseNFunctions = collection.mutable.Map[Integer, (PDomain)]()

  def getDecreaseN(decreaseDomain: PDomain, argsSize: Integer): (PDomain) = {
    if (!decreaseNFunctions.contains(argsSize)) {
      val domainName: String = "DecreasesDomain" + argsSize
      val functionName: String = "decreases"

      val typVars = Seq.tabulate(argsSize)(i => PTypeVarDecl(PIdnDef("T" + i)))

      val vars = typVars.map(t => PFormalArgDecl(PIdnDef("v" + t.idndef.name), PPrimitiv(t.idndef.name)))

      val newDomainFunction = PDomainFunction(PIdnDef(functionName), vars, TypeHelper.Bool, false)(PIdnUse(domainName))
      val newDomain = PDomain(PIdnDef(domainName), typVars, Seq(newDomainFunction), Seq())

      //val newDomainFunction = decreaseDomain.funcs.head.copy(PIdnDef(functionName), vars, TypeHelper.Bool, false)(PIdnUse(domainName))
      //val newDomain = decreaseDomain.copy(PIdnDef(domainName), typVars, Seq(newDomainFunction), Seq())

      //println(decreaseDomain.funcs.head.formalArgs.head.typ.freeTypeVariables)

      //val newDomainFunction = decreaseDomain.funcs.head.copy(formalArgs = vars)(decreaseDomain.funcs.head.domainName)
      //val newDomain = decreaseDomain.copy(typVars = typVars, funcs = Seq(newDomainFunction))

      decreaseNFunctions += (argsSize -> (newDomain))

      (newDomain)
    }else{
      decreaseNFunctions(argsSize)
    }
  }

  /*

  /** Called after identifiers have been resolved but before the parse AST is translated into the normal AST.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeTranslate(input: PProgram): PProgram = {

    // put arguments of decreases calls back
    var newFunctions = Seq[PFunction]()

    for (function <- input.functions){
      val dec = pMapFunctionDecreases.get(function.idndef.name)
      if (dec.isDefined){
        newFunctions = newFunctions :+ function.copy(posts = function.posts :+ dec.get)
      }else{
        newFunctions = newFunctions :+ function
      }
    }

    input.copy(functions = newFunctions)
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

    // add all functions to this sequence
    var newFunctions = Seq[Function]()

    for(function <- input.functions){
      var posts = Seq[Exp]()  // sequence of all post conditions without decreases
      var decs = Seq[Exp]()   // sequence of all post conditions with decreases

      for(post <- function.posts){
        if (post.isInstanceOf[Call] && post.asInstanceOf[Call].callee == "decreases"){
          // the decrease function only has one argument (=> one subExp)
          decs = decs :+ post.subExps.head
          posts = posts :+ post // keep them for pretty print!
        }else{
          posts = posts :+ post
        }
      }

      if (decs.nonEmpty){
        // put all decreases into one DecreaseExp and add it to the postconditions
        posts = posts :+ DecreaseExp(extensionIsPure = true, function.pos, decs)
      }

      // copy the function with the new postconditions
      newFunctions = newFunctions :+ function.copy(posts = posts)(function.pos, function.info, function.errT)
    }

    // copy the program with the new functions
    input.copy(functions = newFunctions)(input.pos, input.info, input.errT)
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
  */
}

case class DecreaseExp(extensionIsPure: Boolean, pos: Position, extensionSubnodes: Seq[Exp]) extends ExtensionExp {

  override def typ: Type = Bool

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */


  override def info: Info = NoInfo

  override def errT: ErrorTrafo = NoTrafos

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  // TODO: !! NO IDEA WHAT TO USE HERE?!?!
  override def prettyPrint: PrettyPrintPrimitives#Cont = ssep(extensionSubnodes map (toParenDoc(_)), char(',') <> space)
}
