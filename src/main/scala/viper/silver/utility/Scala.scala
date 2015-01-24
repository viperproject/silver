/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.utility

/** Utilities that simplify using Scala. */
object Scala {
  trait StructuralEquality { self: AnyRef =>
    protected val equalityDefiningMembers: Seq[Any]

    override val hashCode = generateHashCode(equalityDefiningMembers)

    override def equals(other: Any) = (
         this.eq(other.asInstanceOf[AnyRef])
      || (other match {
            case se: StructuralEquality if this.getClass.eq(se.getClass) =>
              equalityDefiningMembers == se.equalityDefiningMembers
            case _ => false
          }))
  }

  /* Take from scala -print when working with case classes. */
  @inline
  def generateHashCode(xs: Any*) = {
    var code = 0

    for (x <- xs)
      code = code * 41 + (if (x == null) 0 else x.##)

    code
  }
}
