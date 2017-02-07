package viper.silver.ast.utility.Rewriter

/**
  * Created by simonfri on 07.02.2017.
  */
class TRegexAutomaton(val start:State, val end:State) {

}

class State() {
  var transitions = List.empty[Transition]
  var accept = false

  def accepting = accept = true
  def notAccepting = accept = false
  def isAccepting = accept

  def to(target: State): Unit = {
    transitions = new Transition(this, target, None) :: transitions
  }

  def to(target: State, onInput: NMatch[_ <: Rewritable]): Unit = {
    transitions = new Transition(this, target, Some(onInput)) :: transitions
  }

  def performTransition(input: Rewritable): List[State] = {
    val viableTransitions = transitions.filter( t => { if (t.onInput.isDefined) t.onInput.get.matches(input) && t.onInput.get.holds(input) else false  } )
    val transitionTargets:List[State] = viableTransitions.collect { case t:Transition => t.target }
    transitionTargets.flatMap( closure )
  }

  private def closure(states: State): List[State] = {
    val epsilonTransitionTargets = transitions.filter(  _.onInput.isEmpty ).collect { case t:Transition => t.target }
    epsilonTransitionTargets.flatMap(closure)
  }

}

class Transition(val source: State, val target: State, val onInput: Option[NMatch[_]]) {
}


class TransitionInfo {

}

case class MarkedForRewrite() extends TransitionInfo {}

case class ContextInfo() extends TransitionInfo {}

case class NoTransInfo() extends TransitionInfo {}