package viper.silver.plugin.standard.inline

import viper.silver.ast.Node
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.{PartialContext, Rewritable, SimpleContext, Strategy, StrategyInterface, Traverse}

object ViperStrategyCustomTraverse {
  def CustomContextTraverse[C](p: PartialFunction[(Node, C, Node => Node), (Node, C)], initialContext: C): Strategy[Node, ContextCustom[Node, C]] =
    new ViperStrategy[ContextCustom[Node, C]](
      { // rewrite partial function taking context with parent access etc. to one just taking the custom context
        case (node, context) if p.isDefinedAt(node, context.c, context.execute) =>
          val (n, c) = p((node, context.c, context.execute))
          (n, context.updateContext(c))
      }).defaultContext(new PartialContextCC[Node, C](initialContext)).traverse(Traverse.Innermost)
}


// Copy of viper.silver.ast.utility.rewriter with added method
class ContextCustom[N <: Rewritable, CUSTOM](val c: CUSTOM, override protected val transformer: StrategyInterface[N]) extends SimpleContext[N](transformer) {

  // Perform the custom update part of the update
  def updateCustom(n: N): ContextCustom[N, CUSTOM] = {
    new ContextCustom[N, CUSTOM](c, transformer)
  }

  // Update the context with node and custom context
  override def update(n: N): ContextCustom[N, CUSTOM] = {
    updateCustom(n)
  }

  def updateContext(c: CUSTOM) =
    new ContextCustom[N, CUSTOM](c, transformer)

  def execute: N => N = transformer.execute[N]
}

class PartialContextCC[N <: Rewritable, CUSTOM](val custom: CUSTOM) extends PartialContext[N, ContextCustom[N, CUSTOM]] {

  /**
   * Provide the transformer for the real context
   *
   * @param transformer current transformer
   * @return A complete ContextC object
   */
  override def get(transformer: StrategyInterface[N]): ContextCustom[N, CUSTOM] = new ContextCustom[N, CUSTOM](custom, transformer)
}