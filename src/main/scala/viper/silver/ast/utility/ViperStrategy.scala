package viper.silver.ast.utility

import viper.silver.ast._

/**
  * Created by simonfri on 15.12.2016.
  */
class ViperStrategy(rule: PartialFunction[Node, Node]) extends Strategy[Node](rule) {
    cChildren = Transformer.viperChildrenSelector
    duplicator = Transformer.viperDuplicator
}

class ViperStrategyC[C](rule: PartialFunction[(Node, Context[Node, C]), Node]) extends StrategyC[Node, C](rule) {
  cChildren = Transformer.viperChildrenSelector
  duplicator = Transformer.viperDuplicator
}

class ViperQuery[B](getInfo: PartialFunction[Node, B]) extends Query[Node, B](getInfo) {
  cChildren = Transformer.viperChildrenSelector
  duplicator = Transformer.viperDuplicator
}