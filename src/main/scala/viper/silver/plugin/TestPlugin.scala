
package viper.silver.plugin
import viper.silver.parser._

//run --printTranslatedProgram --plugin viper.silver.plugin.TestPlugin silver/src/test/resources/termination/basic/test.vpr
class TestPlugin extends SilverPlugin{
  /** Called after parse AST has been constructed but before identifiers are resolved and the program is type checked.
    *
    * @param input Parse AST
    * @return Modified Parse AST
    */
  override def beforeResolve(input: PProgram): PProgram = {

    println(input.domains)

    // add new Domain with DomainFunction
    val domainName: String = "DecreasesDomain"
    val functionName: String = "decreases"

    val typVars = Seq(PTypeVarDecl(PIdnDef("T")))

    val formalArgs = Seq(PFormalArgDecl(PIdnDef("t"), PPrimitiv("T")))

    val newDomainFunction = PDomainFunction(PIdnDef(functionName), formalArgs, TypeHelper.Bool, false)(PIdnUse(domainName))
    val newDomain = PDomain(PIdnDef(domainName), typVars, Seq(newDomainFunction), Seq())

    val newProgram = PProgram(
      input.imports,
      input.macros,
      input.domains :+ newDomain,
      input.fields,
      input.functions,
      input.predicates,
      input.methods,
      input.errors
    )

    println(newProgram.domains.tail)

    newProgram
  }
}