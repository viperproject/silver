package viper.silver.ast.utility.Rewriter

/**
  * Created by simonfri on 07.02.2017.
  */

// Encapsulation of start and end state in an automaton to make it expandable
class TRegexAutomaton(val start:State, val end:State)

class MatchState() extends State {
  var matchTransition: Option[Transition] = None

  def toMatch(target: EpsilonState, onInput: NMatch[_ <: Rewritable]): Unit = {
    matchTransition = Some(new Transition(this, target, Some(onInput)))
  }

  def performTransition(input: Rewritable): (List[MatchState], TransitionInfo) = {
    matchTransition match {
      case None => (eTransitions.map( _.target).flatMap( closure ), NoTransInfo())
      case Some(t) => {
        if(t.onInput.isDefined && t.onInput.get.holds(input)) {
          (t.target.performTransition()._1, t.onInput.get.getTransitionInfo(input))
        } else {
          (Nil, NoTransInfo())
        }
      }
    }
  }

}

class EpsilonState extends State {}

abstract class State() {
  var eTransitions = List.empty[Transition]

  var accept = false

  def accepting() = accept = true
  def notAccepting() = accept = false
  def isAccepting = accept



  def to(target: State): Unit = {
    eTransitions = new Transition(this, target, None) :: eTransitions
  }



  def performTransition(): (List[MatchState], TransitionInfo) = {
    val transitionTargets:List[State] = eTransitions.collect { case t:Transition => t.target }
    (transitionTargets.flatMap( closure ), NoTransInfo())
  }

  protected def closure(state: State): List[MatchState] = {
    state match {
      case m:MatchState => List(m)
      case s:State => {
        eTransitions.map( _.target).flatMap( closure )
      }
    }
  }

}

class Transition(val source: State, val target: State, val onInput: Option[NMatch[_]]) {

}


class TransitionInfo {

}

case class ChildSelectInfo(ch: Rewritable) extends TransitionInfo {}

case class MarkedForRewrite() extends TransitionInfo {}

case class ContextInfo(c: Any) extends TransitionInfo {}

case class NoTransInfo() extends TransitionInfo {}