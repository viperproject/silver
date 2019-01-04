
package viper.silver.plugin

import viper.silver.ast.{Node, Program}


// run --printTranslatedProgram --plugin viper.silver.plugin.DecreasePlugin silver/src/test/resources/termination/basic/adt.sil
class DecreasePlugin extends SilverPlugin
{

  private var members = collection.mutable.HashMap[String, Node]()

  /** Called after parse AST has been translated into the normal AST but before methods to verify are filtered.
    * In [[viper.silver.frontend.SilFrontend]] this step is confusingly called doTranslate.
    *
    * @param input AST
    * @return Modified AST
    */
  override def beforeMethodFilter(input: Program): Program = {

    // Add methods, domains and functions needed for proving termination

    val locDom = input.domains.find(d => d.name.equals("Loc"))

    val decFunc = input.findDomainFunctionOptionally("decreasing")
    val boundFunc = input.findDomainFunctionOptionally("bounded")
    val nestFunc = input.findDomainFunctionOptionally("nested")

    val termCheck = new DecreasesClause2(input)
    val structureForTermProofs = termCheck.addMethods(input.functions, input.predicates, input.domains, decFunc, boundFunc, nestFunc, locDom)

    val d = structureForTermProofs._1
    val f = structureForTermProofs._2
    val m = structureForTermProofs._3

    input.copy(domains = d, functions = input.functions ++ f, methods = input.methods ++ m)(input.pos, input.info, input.errT)

  }

}
