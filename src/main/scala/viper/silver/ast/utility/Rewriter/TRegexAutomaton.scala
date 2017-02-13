package viper.silver.ast.utility.Rewriter

/**
  * Created by simonfri on 07.02.2017.
  */

// Encapsulation of start and end state in an automaton to make it expandable
class TRegexAutomaton(val start:State, val end:State)

class State(private var mTrans:Option[MTransition] = None, private var eTrans:Seq[ETransition] = Seq.empty[ETransition]) {

  // Don't make this immutable because constructing a circle out of immutable objects is cumbersome
  def setMTrans(to: State, matcher: NMatch[_]) = {
    mTrans = Some(new MTransition(this, to, matcher))
  }

  def addETrans(to: State) = {
    eTrans ++= Seq(new ETransition(this, to))
    effectiveCache = Set.empty[State]
  }
  // Epsilon state denotes that we will only be passed through and don't really exist in the reduced state machine
  def isEpsilonState = mTrans.isEmpty

  def isEffectiveState = !isEpsilonState || isAccepting
  // A state is accepting if it does not have any further transitions. Then the Regex is recognized
  def isAccepting = eTrans.isEmpty && mTrans.isEmpty

  def isValidInput(input: Rewritable): Boolean = {
    mTrans match {
      case None => false
      case Some(m) => m.matcher.holds(input)
    }
  }

  def performTransition(n: Rewritable):(Set[State], Seq[TransitionInfo]) = {
    mTrans match {
      case None =>
        println("Error. Cannot perform transition with input on an epsilon state")
        (Set.empty[State], Seq.empty[TransitionInfo])
      case Some(t) if !t.matcher.holds(n) =>
        (Set.empty[State], Seq.empty[TransitionInfo])
      case Some(t) =>
        val infos = t.matcher.getTransitionInfo(n)
        val states = t.target.effective
        (states ,infos)
    }
  }

  // Effective is every state that includes at least one match transition
  // Find out every effective state that is reachable from this state. Cache the computed result
  private var effectiveCache: Set[State] = Set.empty[State]
  def effective: Set[State] = {
    if(effectiveCache.isEmpty) {
      effectiveCache = allStates(Set.empty[State]).filter( _.isEffectiveState)
    }
    effectiveCache
  }

  def allStates(collected: Set[State]): Set[State] = {
    if(collected.contains(this)) {
      collected
    } else if(eTrans.isEmpty) {
      Set(this) ++ collected
    }
    else {
      eTrans.map({ eT => eT.target.allStates(Set(this) ++ collected) }).foldLeft(Set.empty[State])( (s, set) => set ++ s)
    }
  }
}

abstract class Transition {
  def source: State
  def target: State

  def getActions(n: Rewritable): Seq[TransitionInfo]
}

class ETransition(val source: State, val target: State) extends Transition {
  override def getActions(n: Rewritable): Seq[TransitionInfo] = Seq.empty[TransitionInfo]
}

class MTransition(val source: State, val target: State, val matcher: NMatch[_]) extends Transition {
  override def getActions(n: Rewritable): Seq[TransitionInfo] = matcher.getTransitionInfo(n)
}



class TransitionInfo

case class ChildSelectInfo(ch: Rewritable) extends TransitionInfo {}

case class MarkedForRewrite() extends TransitionInfo {}

case class ContextInfo(c: Any) extends TransitionInfo {}