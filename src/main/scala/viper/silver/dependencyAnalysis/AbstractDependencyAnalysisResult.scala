package viper.silver.dependencyAnalysis

import viper.silver.ast.Program

abstract class AbstractDependencyAnalysisResult(programName: String, program: Program, dependencyGraphInterpreters: Iterable[AbstractDependencyGraphInterpreter]) {

  def getFullDependencyGraphInterpreter: AbstractDependencyGraphInterpreter
}
