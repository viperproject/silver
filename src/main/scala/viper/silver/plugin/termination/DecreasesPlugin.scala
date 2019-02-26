
package viper.silver.plugin.termination

import viper.silver.ast._
import viper.silver.ast.utility.{Functions, ViperStrategy}
import viper.silver.parser._
import viper.silver.plugin.SilverPlugin
import viper.silver.plugin.termination.proofcode._
import viper.silver.verifier.errors.AssertFailed
import viper.silver.verifier.{ConsistencyError, Failure, Success, VerificationResult}

// run --printTranslatedProgram --plugin viper.silver.plugin.DecreasePlugin silver/src/test/resources/termination/basic/test.vpr
trait DecreasesPlugin extends SilverPlugin {

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
    val decreasesStarFunction = PDomainFunction(PIdnDef(decreasesStar), Nil, PPrimitiv(TypeHelper.Bool.name), unique = false)(domainIdUse)

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
        PDomainFunction(PIdnDef(functionName), formalArgs.take(argsSize), PPrimitiv(TypeHelper.Bool.name), unique = false)(domainIdUse)
    }.toSeq

    // all needed predicate functions
    val predicateFunctions: Seq[PDomainFunction] = predicates.map {
      case ((_, args), function) =>
        PDomainFunction(PIdnDef(function), args, PPrimitiv(TypeHelper.Bool.name), unique = false)(domainIdUse)
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
      case p: Program =>
        // remove the helper domain
        val domains = p.domains.filterNot(d => d.name.equals(helperDomain))
        p.copy(domains = domains)(p.pos, p.info, p.errT)
      case f: Function =>
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
    transformToCheckProgram(newProgram, decreasesMap)
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

  /**
    * Creates a Program containing all the wanted termination checks
    * @param input program
    * @param decreasesMap all decreases exp (defined by the user)
    * @return a program with the additional termination checks (including normal program)
    */
  def transformToCheckProgram(input: Program, decreasesMap: Map[Function, DecreasesExp]): Program

  private def checkNoFunctionRecursesViaDecreasesClause(program: Program): Seq[ConsistencyError] = {

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

  private def removeDecreaseExp(program: Program): (Program, Map[Function, DecreasesExp]) = {
    val decreaseMap = scala.collection.mutable.Map[Function, DecreasesExp]()

    val result: Program = ViperStrategy.Slim({
      case f: Function =>
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
    }).execute(program)
    (result, decreaseMap.toMap)
  }
}
