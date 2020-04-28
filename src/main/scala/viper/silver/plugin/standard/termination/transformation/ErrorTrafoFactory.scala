// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import viper.silver.ast.ReTrafo
import viper.silver.plugin.standard.termination.{TerminationConditionFalse, TupleBoundedFalse, TupleConditionFalse, TupleDecreasesFalse, TupleSimpleFalse}
import viper.silver.verifier.reasons.{AssertionFalse, ErrorNode}

/**
 * Interface for factories creating error/reason trafos.
 */
trait AbstractReasonTrafoFactory {
  def generateTerminationConditionFalse(offendingNode: ErrorNode): ReTrafo

  def generateTupleConditionFalse(offendingNode: ErrorNode): ReTrafo

  def generateTupleSimpleFalse(offendingNode: ErrorNode): ReTrafo

  def generateTupleDecreasesFalse(offendingNode: ErrorNode): ReTrafo

  def generateTupleBoundedFalse(offendingNode: ErrorNode): ReTrafo
}

case class ReasonTrafoFactory(offendingNode: ErrorNode) extends AbstractReasonTrafoFactory {

  override def generateTerminationConditionFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TerminationConditionFalse(offendingNode) })
  }

  override def generateTupleConditionFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TupleConditionFalse(offendingNode) })
  }

  override def generateTupleSimpleFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TupleSimpleFalse(offendingNode) })
  }

  override def generateTupleDecreasesFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TupleDecreasesFalse(offendingNode) })
  }

  override def generateTupleBoundedFalse(offendingNode: ErrorNode = offendingNode): ReTrafo = {
    ReTrafo({ case AssertionFalse(_) => TupleBoundedFalse(offendingNode) })
  }
}