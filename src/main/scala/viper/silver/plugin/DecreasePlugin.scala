
package viper.silver.plugin

import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, space, ssep, text, toParenDoc}
import viper.silver.ast.utility.{Consistency, Functions, ViperStrategy}
import viper.silver.parser._
import viper.silver.verifier.ConsistencyError

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

    val newFunctions = collection.mutable.ArrayBuffer[PFunction]()

    for(function <- input.functions){
      val posts = collection.mutable.ArrayBuffer[PExp]()
      for(post <- function.posts){
        post match {
          case call: PCall if call.opName.equals(DECREASES)=>{
              // change call
              val argsSize = call.args.length
              val functionName = getDecreasesNFunction(argsSize)
              val post = call.copy(func = PIdnUse(functionName)).setPos(call)
              posts.append(post)
            }
          case _ =>
            posts.append(post)
        }
      }

      val newFunction = function.copy(posts = posts).setPos(function)
      newFunctions.append(newFunction)
    }

    if (decreasesNFunctions.nonEmpty) {
      val newDomain = createDecreasesDomain(getDecreasesNDomain, decreasesNFunctions.toMap)
      input.copy(functions = newFunctions, domains = input.domains :+ newDomain)
    }else{
      input
    }
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
    // get decrease in post conditions and
    // transform them to post condition with a DecreaseExp
    transformDecreasesNToDecreaseExp(input, decreasesNFunctions.toMap, getDecreasesNDomain)
  }

  /** Called after methods are filtered but before the verification by the backend happens.
    *
    * @param input AST
    * @return Modified AST
    */
  override def beforeVerify(input: Program): Program = {
    // remove all post conditions which are DecreaseExp
    // and add them to the decreaseMap functions -> decreases map


    val errors = checkNoFunctionRecursesViaDecreasesClause(input)
    if (errors.nonEmpty){
      for (e <- errors) {
        reportError(e)
      }
      return input
    }

    val removedDecreasesExp = removeDecreaseExp(input)

    val newProgram: Program = removedDecreasesExp._1
    val decreasesMap = removedDecreasesExp._2


    val locDom = newProgram.domains.find(d => d.name.equals("Loc"))
    val decFunc = newProgram.findDomainFunctionOptionally("decreasing")
    val boundFunc = newProgram.findDomainFunctionOptionally("bounded")
    val nestFunc = newProgram.findDomainFunctionOptionally("nested")

    val termCheck = new DecreasesClause2(newProgram, decreasesMap)
    val structureForTermProofs = termCheck.addMethods(newProgram.functions, newProgram.predicates, newProgram.domains, decFunc, boundFunc, nestFunc, locDom)

    val d = structureForTermProofs._1
    val f = structureForTermProofs._2
    val m = structureForTermProofs._3

    newProgram.copy(domains = d, functions = newProgram.functions ++ f, methods = newProgram.methods ++ m)(newProgram.pos, newProgram.info, newProgram.errT)
  }


  def transformDecreasesNToDecreaseExp(input: Program, decreasesNFunctions: Map[Integer, String], decreasesNDomain: String): Program = {
    ViperStrategy.Slim({
      case p: Program => {
        val domains = p.domains.filterNot(d => d.name.equals(decreasesNDomain))
        p.copy(domains = domains)(p.pos, p.info, p.errT)
      }
      case f: Function => {
        val posts = f.posts map {
          case c: Call if decreasesNFunctions.get(c.args.size).contains(c.callee) => {
            DecreaseExp(c.isPure, c.pos, c.subExps, NodeTrafo(c))
          }
          case p => p
        }
        Function(
          name = f.name,
          posts = posts,
          formalArgs = f.formalArgs,
          typ = f.typ,
          pres = f.pres,
          decs = f.decs,
          body = f.body,
        )(f.pos, f.info, NodeTrafo(f))
      }
    }).execute(input)
  }

  def removeDecreaseExp(program: Program): (Program, Map[Function, DecreaseExp]) = {
    val decreaseMap = scala.collection.mutable.Map[Function, DecreaseExp]()

    val result: Program = ViperStrategy.Slim({
      case f: Function => {
        val partition = f.posts.partition(p => p.isInstanceOf[DecreaseExp])
        val decreases = partition._1
        val posts = partition._2

        val newFunction =
          Function(
            name = f.name,
            posts = posts,
            formalArgs = f.formalArgs,
            typ = f.typ,
            pres = f.pres,
            decs = f.decs,
            body = f.body,
          )(f.pos, f.info, NodeTrafo(f))

        if (decreases.nonEmpty) {
          decreaseMap += (newFunction -> decreases.head.asInstanceOf[DecreaseExp])
        }
        newFunction
      }
    }).execute(program)
    (result, decreaseMap.toMap)
  }

  def checkNoFunctionRecursesViaDecreasesClause(program: Program): Seq[ConsistencyError] = {

    val checkProgram: Program = ViperStrategy.Slim({
      case f: Function => {
        val partition = f.posts.partition(p => p.isInstanceOf[DecreaseExp])
        val decreases = partition._1
        val posts = partition._2

        val newFunction =
          Function(
            name = f.name,
            posts = posts,
            formalArgs = f.formalArgs,
            typ = f.typ,
            pres = f.pres ++ decreases,
            decs = f.decs,
            body = f.body,
          )(f.pos, f.info, NodeTrafo(f))
        newFunction
      }
    }).execute(program)

    // TODO WHY??
    var errors = Seq.empty[ConsistencyError]
    Functions.findFunctionCyclesViaPreconditions(checkProgram) foreach { case (func, cycleSet) =>
      var msg = s"Function ${func.name} recurses via its decreases clause"

      if (cycleSet.nonEmpty) {
        msg = s"$msg: the cycle contains the function(s) ${cycleSet.map(_.name).mkString(", ")}"
      }
      errors :+= ConsistencyError(msg, func.pos)
    }
    errors
  }
}

case class DecreaseExp(extensionIsPure: Boolean, pos: Position, extensionSubnodes: Seq[Exp], errT: ErrorTrafo) extends ExtensionExp {

  override def typ: Type = Bool

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */

  override def info: Info = NoInfo

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
      case Seq(args: List[Exp]) => DecreaseExp(extensionIsPure, pos, args, errT)
    }
  }
}
