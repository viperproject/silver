/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.ast._

/** Utility methods for permissions. */
object Permissions {
  def positivityConstraints(exp: Exp): Seq[Exp] = {
    assert(exp.typ == Perm,
           "Expected expression of type Perm, but found %s (%s)".format(exp.typ, exp.typ.getClass.getName))

    val constraints = if (isConditional(exp)) Nil else Seq(exp)

    assert(constraints forall (_.typ == Perm),
           "Expected all expressions to be of type Perm (in %s)".format(constraints))

    constraints
  }

  def isConditional(exp: Exp) = exp existsDefined {
    case _: CondExp =>
  }
}
