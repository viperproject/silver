
package viper.silver.plugin.termination

import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, space, ssep, text, toParenDoc}
import viper.silver.ast.utility.{Functions, ViperStrategy}
import viper.silver.parser._
import viper.silver.plugin.SilverPlugin
import viper.silver.verifier.errors.AssertFailed
import viper.silver.verifier.{ConsistencyError, Failure, Success, VerificationResult}

// run --printTranslatedProgram --plugin viper.silver.plugin.DecreasePlugin silver/src/test/resources/termination/basic/test.vpr
class DecreasePlugin extends SilverPlugin {

  // decreases keywords
  private val DECREASES = "decreases"
  private val DECREASESSTAR = "decreasesStar"

  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
    * Replaces all decreases function calls in postconditions, replaces them with decreasesN function calls and
    * adds a domain with the necessary decreasesN functions.
    * Replaces all predicates acc in decreases function calls, replaces them with function calls.
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeResolve(input: PProgram): PProgram = {
    // replace all decreases (calls in postconditions)
    // with decreasesN calls
    // and add DecreasesDomain with all needed decreasesN functions

    val functions = input.functions.map(function => {
      val posts = function.posts.map({
          case call: PCall if call.opName.equals(DECREASES)=>
            // replace call
            val argsSize = call.args.length
            val functionName = addDecreasesNFunction(argsSize)
            // replace predicates
            val newArgs = call.args.map {
              case call: PCall if input.predicates.map(_.idndef.name).contains(call.idnuse.name) =>
                // a predicate with the same name exists
                val predicate = input.predicates.filter(_.idndef.name.equals(call.idnuse.name)).head
                val formalArg = predicate.formalArgs
                // use the same arguments to type check!
                val function = addPredicateFunctions(call.idnuse.name, formalArg)
                call.copy(func = PIdnUse(function)).setPos(call)
              case default => default
            }
            call.copy(func = PIdnUse(functionName), args = newArgs).setPos(call)
          case call: PCall if call.opName.equals(DECREASESSTAR) =>
            call.copy(func = PIdnUse(getDecreasesStarFunction)).setPos(call)
          case d => d
      })
      function.copy(posts = posts).setPos(function)
    })

    val domains = input.domains :+ {
      createHelperDomain(getHelperDomain, getDecreasesStarFunction,decreasesNFunctions.toMap, predicateFunctions.toMap)
    }

    input.copy(functions = functions, domains = domains).setPos(input)
  }

  private def getDecreasesStarFunction: String = {
    "$decreasesStar"
  }

  /**
    * All needed decreasesN functions with N arguments
    * (N -> decreasesNFunction name)
    * Has to be invertible
    */
  private val decreasesNFunctions = collection.mutable.Map[Integer, String]()

  /**
    * Lazy map using the decreasesNFunctions
    * @param argsSize: number of arguments needed
    * @return name of decrease function
    */
  private def addDecreasesNFunction(argsSize: Integer): String = {
    if (!decreasesNFunctions.contains(argsSize)){
      val newName: String = s"$$decreases$argsSize"
      decreasesNFunctions(argsSize) = newName
    }
    decreasesNFunctions(argsSize)
  }

  /**
    * All needed functions representing a predicate in the decrease clause
    * ((predicateName, argumentNumber) -> functionName)
    * Has to be invertible
    */
  private val predicateFunctions = collection.mutable.Map[(String, Seq[PFormalArgDecl]), String]()

  private  def addPredicateFunctions(predicateName: String, args: Seq[PFormalArgDecl]): String = {
    if (!predicateFunctions.contains((predicateName, args))){
      val functionName: String = s"$$pred_$predicateName"
      predicateFunctions((predicateName, args)) = functionName
    }
    predicateFunctions((predicateName, args))
  }

  private def getHelperDomain: String = {
    "$HelperDomain"
  }

  private def createHelperDomain(name: String, decreasesStar: String,
                                 decreasesN: Map[Integer, String],
                                 predicates: Map[(String, Seq[PFormalArgDecl]), String]): PDomain = {
    val domainIdDef = PIdnDef(name)
    val domainIdUse = PIdnUse(name)

    // decreases star domain function
    val decreasesStarFunction = PDomainFunction(PIdnDef(decreasesStar), Nil, PPrimitiv(TypeHelper.Bool.name), false)(domainIdUse)

    // number of type parameters needed
    val maxArgs: Integer = decreasesN.keySet match {
      case d if d.isEmpty => 0
      case d => d.max
    }
    // all type parameters
    val typeVars = Seq.tabulate(maxArgs)(i => PTypeVarDecl(PIdnDef(s"T$i")))
    // list of arguments with the type parameter
    val formalArgs: Seq[PFormalArgDecl] = typeVars.map(t => PFormalArgDecl(PIdnDef(s"v${t.idndef.name}"), PDomainType(PIdnUse(t.idndef.name), Seq())))
    // all needed decreasesN functions
    val decreasesFunctions: Seq[PDomainFunction] = decreasesN.map {
      case (argsSize, functionName) =>
        PDomainFunction(PIdnDef(functionName), formalArgs.take(argsSize), PPrimitiv(TypeHelper.Bool.name), false)(domainIdUse)
    }.toSeq

    // all needed predicate functions
    val predicateFunctions: Seq[PDomainFunction] = predicates.map {
      case ((predicate, args), function) =>
        PDomainFunction(PIdnDef(function), args, PPrimitiv(TypeHelper.Bool.name), false)(domainIdUse)
    }.toSeq

    PDomain(domainIdDef, typeVars, decreasesFunctions ++ predicateFunctions :+ decreasesStarFunction , Seq())
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
    // also transform all functions representing predicates back

    val helperDomain = getHelperDomain
    val decStarFunc = getDecreasesStarFunction
    val decNFuncInverted = decreasesNFunctions.toMap.map(_.swap)
    val predFuncInverted = predicateFunctions.toMap.map(_.swap)


    ViperStrategy.Slim({
      case p: Program => {
        // remove the helper domain
        val domains = p.domains.filterNot(d => d.name.equals(helperDomain))
        p.copy(domains = domains)(p.pos, p.info, p.errT)
      }
      case f: Function => {
        val posts = f.posts map {
          case c: Call if c.callee.equals(decStarFunc) =>
            // replace all decreasesStar functions with DecreasesStar
            DecreasesStar(c.pos, NodeTrafo(c))
          case c: Call if decNFuncInverted.contains(c.callee) =>
            // replace all decreasesN functions with DecreasesTuple
            assert(c.args.size == decNFuncInverted(c.callee))
            val newArgs = c.args map {
              // replace all predicate functions with the PredicateAccess
              case p: Call if predFuncInverted.contains(p.callee) =>
                val mapResult = predFuncInverted(p.callee)
                assert(p.args.size == mapResult._2.size)
                PredicateAccess(p.args, mapResult._1)(p.pos, p.info, p.errT)
              case default => default
            }
            DecreasesTuple(newArgs, c.pos, NodeTrafo(c))
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
        )(f.pos, f.info, f.errT)
      }
    }).execute(input)

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
    //val removedDecreasesExp = getDecreaseExpFromDecrease(input)

    val newProgram: Program = removedDecreasesExp._1
    val decreasesMap = removedDecreasesExp._2
    transformToVerifiableProgramPath(newProgram, decreasesMap)
  }


  /** Called after the verification. Error transformation should happen here.
    * This will only be called if verification took place.
    *
    * @param input Result of verification
    * @return Modified result
    */
  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Success => input
      case Failure(errors) => Failure(errors.map({
        case a@AssertFailed(Assert(_), _, _) => a.transformedError()
        case e => e
      }))
    }
  }

  def transformToVerifiableProgramSimple(input: Program, decreasesMap: Map[Function, DecreasesExp]): Program = {
    val termCheck = new SimpleDecreases(input, decreasesMap)
    termCheck.createCheckProgram()
  }

  def transformToVerifiableProgramPath(input: Program, decreasesMap: Map[Function, DecreasesExp]): Program = {
    val termCheck = new DecreasesPlus(input, decreasesMap)
    termCheck.createCheckProgram()
  }

  /*
  def transformToVerifiableProgram(input: Program, decreasesMap: Map[Function, DecreasesExp]): Program = {

    val heights = Functions.heights(input)

    val locDom = input.domains.find(d => d.name.equals("Loc"))
    val decFunc = input.findDomainFunctionOptionally("decreasing")
    val boundFunc = input.findDomainFunctionOptionally("bounded")
    val nestFunc = input.findDomainFunctionOptionally("nested")

    val termCheck = new DecreasesClause2(input, decreasesMap)
    val structureForTermProofs = termCheck.addMethods(input.functions, input.predicates, input.domains, decFunc, boundFunc, nestFunc, locDom)

    val d = structureForTermProofs._1
    val f = structureForTermProofs._2
    val m = structureForTermProofs._3

    //newProgram.copy(domains = d, functions = newProgram.functions ++ f, methods = newProgram.methods ++ m)(newProgram.pos, newProgram.info, newProgram.errT)

    Program(
      d,
      input.fields,
      input.functions ++ f,
      input.predicates,
      input.methods ++ m
    )(input.pos, input.info, input.errT)
  }
  */

  def removeDecreaseExp(program: Program): (Program, Map[Function, DecreasesExp]) = {
    val decreaseMap = scala.collection.mutable.Map[Function, DecreasesExp]()

    val result: Program = ViperStrategy.Slim({
      case f: Function => {
        val partition = f.posts.partition(p => p.isInstanceOf[DecreasesExp])
        val decreases = partition._1
        val posts = partition._2

        if (decreases.size == 1) {
          val newFunction =
            Function(
              name = f.name,
              posts = posts,
              formalArgs = f.formalArgs,
              typ = f.typ,
              pres = f.pres,
              decs = f.decs,
              body = f.body,
            )(f.pos, f.info, f.errT)

          if (decreases.nonEmpty) {
            decreaseMap += (newFunction -> decreases.head.asInstanceOf[DecreasesExp])
          }
          newFunction
        }else if (decreases.nonEmpty){
          // more than one decreases clause
          reportError(ConsistencyError("More than one decreases clauses are defined.", f.pos))
          f
        } else {
          // none decreases clause
          f
        }
      }
    }).execute(program)
    (result, decreaseMap.toMap)
  }

  /**
    * ONLY FOR TESTS!
    * @param program
    * @return
    */
  def getDecreaseExpFromDecrease(program: Program): (Program, Map[Function, DecreasesExp]) = {
    val decreaseMap: Map[Function, DecreasesExp] =
      program.functions.filter(_.decs.nonEmpty).map(f => f.decs.get match {
        case ds@DecStar() => f -> DecreasesStar(ds.pos, NodeTrafo(ds))
        case d@DecTuple(e) => f -> DecreasesTuple(d.exp, d.pos, NodeTrafo(d))
      }).toMap

    (program, decreaseMap)
  }

  def checkNoFunctionRecursesViaDecreasesClause(program: Program): Seq[ConsistencyError] = {

    def functionDecs(function:Function) = function.posts.filter(p => p.isInstanceOf[DecreasesExp])

    var errors = Seq.empty[ConsistencyError]
    Functions.findFunctionCyclesVia(program, functionDecs) foreach { case (func, cycleSet) =>
      var msg = s"Function ${func.name} recurses via its decreases clause"

      if (cycleSet.nonEmpty) {
        msg = s"$msg: the cycle contains the function(s) ${cycleSet.map(_.name).mkString(", ")}"
      }
      errors :+= ConsistencyError(msg, func.pos)
    }
    errors
  }
}

sealed trait DecreasesExp extends ExtensionExp with Node

case class DecreasesTuple(extensionSubnodes: Seq[Exp] = Nil, pos: Position = NoPosition, errT: ErrorTrafo = NoTrafos) extends DecreasesExp {

  override def extensionIsPure = true

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

  override def duplicate(children: Seq[AnyRef]): DecreasesTuple = {
    children match {
      case Seq(args: List[Exp]) => DecreasesTuple(args, pos, errT)
    }
  }
}

case class DecreasesStar(pos: Position = NoPosition, errT: ErrorTrafo = NoTrafos) extends DecreasesExp{
  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Nil

  override def typ: Type = Bool

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = text("decreasesStar")

  override def info: Info = NoInfo

}
