package viper.silver.plugin.standard.decreases.transformation

import viper.silver.ast.ReTrafo
import viper.silver.plugin.standard.decreases.{TerminationConditionFalse, TupleBoundedFalse, TupleConditionFalse, TupleDecreasesFalse, TupleSimpleFalse}
import viper.silver.verifier.reasons.{AssertionFalse, ErrorNode}

/**
 * Interface for factories creating trafos (plugin/rewrite system) of non-termination reasons.
 */
trait AbstractReasonTrafoFactory{
  def generateTerminationConditionFalse(offendingNode: ErrorNode): ReTrafo
  def generateTupleConditionFalse(offendingNode: ErrorNode): ReTrafo
  def generateTupleSimpleFalse(offendingNode: ErrorNode): ReTrafo
  def generateTupleDecreasesFalse(offendingNode: ErrorNode): ReTrafo
  def generateTupleBoundedFalse(offendingNode: ErrorNode): ReTrafo
}

//### SIMPLE REASONS ###
case class ReasonTrafoFactory(offendingNode: ErrorNode) extends AbstractReasonTrafoFactory {

  override def generateTerminationConditionFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TerminationConditionFalse(offendingNode)})
  }

  override def generateTupleConditionFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TupleConditionFalse(offendingNode)})
  }

  override def generateTupleSimpleFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TupleSimpleFalse(offendingNode)})
  }

  override def generateTupleDecreasesFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TupleDecreasesFalse(offendingNode)})
  }

  override def generateTupleBoundedFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TupleBoundedFalse(offendingNode)})
  }
}