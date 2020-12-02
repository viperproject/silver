package viper.silver.plugin.standard.inline

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.Program
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

class InlinePredicatePlugin extends SilverPlugin with ParserPluginTemplate with InlineRewrite {

  private[this] val InlinePredicateKeyword = "inline"

  override def beforeVerify(input: Program): Program = {
    val rewrittenMethods = input.methods.map { method =>
      val (prePredIds, postPredIds) = getPrePostPredIds(method, input)
      val inlinedPredMethod = inlinePredicates(method, input, prePredIds, postPredIds)
      rewriteMethod(inlinedPredMethod, input, prePredIds, postPredIds)
    }
    ViperStrategy.Slim({
      case program@Program(_, _, _, _, methods, _) =>
        program.copy(methods = rewrittenMethods
        )(program.pos, program.info, program.errT)
    }).execute[Program](input)
  }
}
