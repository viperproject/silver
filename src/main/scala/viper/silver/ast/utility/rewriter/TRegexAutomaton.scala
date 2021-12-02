// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility.rewriter


// Encapsulation of start and end state in an automaton to make it expandable
class TRegexAutomaton(val start:State, val end:State)

// State encapsulates the point where the current transition is in.
// mTrans: Contains zero or one matching transitions (transitions that include a match)
// eTrans: Contains a list of epsilon transitions (transitions that always match)
class State(private var mTrans:Option[MTransition] = None, private var eTrans:Seq[ETransition] = Seq.empty[ETransition]) {

  // Setter for mTrans
  def setMTrans(to: State, matcher: NMatch[_]) = {
    mTrans = Some(new MTransition(this, to, matcher))
  }

  // Add another ETrans
  def addETrans(to: State) = {
    eTrans ++= Seq(new ETransition(this, to))
    // Reset the effective states cache. It might change with a new epsilon transition
    effectiveCache = Set.empty[State]
  }

  // A state is an epsilon state if it has no matching transformations and is not accepting (it will only be passed through and does not capture a real state)
  def isEpsilonState = mTrans.isEmpty && !isAccepting

  // A state is an effective state if it is not an epsilon state
  def isEffectiveState = !isEpsilonState

  // A state is accepting if it does not have any further transitions. All matching transitions were already taken
  def isAccepting = eTrans.isEmpty && mTrans.isEmpty

  // Find out if parameter input has a valid transition
  def isValidInput(input: Rewritable): Boolean = {
    mTrans match {
      case None => false
      case Some(m) => m.matcher.holds(input)
    }
  }

  // Perform the next transition with input n
  // Result: Set of new states we are in and the resulting action from our transition
  def performTransition(n: Rewritable):(Set[State], Seq[TransitionInfo]) = {
    mTrans match {
      case None =>
        // We should never get here if everything works as intended
        throw new AssertionError("Cannot perform transition with input on an epsilon state")
      case Some(t) if !t.matcher.holds(n) =>
        // If matcher does not hold we are in no state anymore and done (kind of the error state)
        (Set.empty[State], Seq.empty[TransitionInfo])
      case Some(t) =>
        // Everything fine. Perform transition
        val infos = t.matcher.getTransitionInfo(n)
        val states = t.target.effective
        (states ,infos)
    }
  }

  // Find out every effective state that is reachable from this state via epsilon transitions. Cache the computed result for efficiency
  private var effectiveCache: Set[State] = Set.empty[State]
  def effective: Set[State] = {
    if(effectiveCache.isEmpty) {
      effectiveCache = allStates(Set.empty[State]).filter( _.isEffectiveState)
    }
    effectiveCache
  }

  // Helper function to compute all the reachable states
  private def allStates(collected: Set[State]): Set[State] = {
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

// Encapsulate the needed information for a transition (source, target)
abstract class Transition {
  def source: State
  def target: State

  def getActions(n: Rewritable): Seq[TransitionInfo]
}

// Epsilon transition. Matches on everything
class ETransition(val source: State, val target: State) extends Transition {
  override def getActions(n: Rewritable): Seq[TransitionInfo] = Seq.empty[TransitionInfo]
}

// Matching transition. Can only be taken if the input node matches on the matcher
class MTransition(val source: State, val target: State, val matcher: NMatch[_]) extends Transition {
  override def getActions(n: Rewritable): Seq[TransitionInfo] = matcher.getTransitionInfo(n)
}


// Encapsulate information that is generated when taking transition.
class TransitionInfo

// Information about the children we want to recurse into
case class ChildSelectInfo(ch: Rewritable) extends TransitionInfo {}

// Marks a node for rewriting
case class MarkedForRewrite() extends TransitionInfo {}

// Information about the extracted context
case class ContextInfo(c: Any) extends TransitionInfo {}