package viper.silver.plugin.termination
import viper.silver.ast
import viper.silver.ast.Program
import viper.silver.plugin.termination.checkcode.{CheckDecreasesSimple, DecreasesExp}


class DecreasesSimple extends DecreasesPlugin {
  override def transformToCheckProgram(input: Program, decreasesMap: Map[ast.Function, DecreasesExp]): Program = {
    val termCheck = new CheckDecreasesSimple(input, decreasesMap)
    termCheck.createCheckProgram()
  }
}