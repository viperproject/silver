package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.Program
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

class InlinePredicatePlugin extends SilverPlugin with ParserPluginTemplate with InlineRewrite {

  private[this] val InlinePredicateKeyword = "inline"

  override def beforeVerify(input: Program): Program = {
    val declaredMethods = input.methods
    val methodsWithInlinedPreds = declaredMethods.map(inlinePredicates(_, input))
    val rewrittenMethods = methodsWithInlinedPreds.map(removeUnfoldFold(_, input))

    // TODO: actually rewrite program with methods with expanded predicates
    val rewrittenProgram = ViperStrategy.Slim({
      case program: Program =>
        program.copy(methods = rewrittenMethods)(program.pos, program.info, program.errT)
    }, Traverse.BottomUp).execute(input)
    rewrittenProgram
  }
}
