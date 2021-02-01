// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.silver.ast.utility

import scala.collection.mutable

/** A trait for traversable collections. */
trait Traversable[+A] {
  self =>

  /** Applies a function to all element of the collection. */
  def foreach[B](f: A => B): Unit

  /** Creates a filter of this traversable collection. */
  def withFilter(p: A => Boolean): Traversable[A] = new WithFilter(p)

  class WithFilter(p: A => Boolean) extends Traversable[A] {
    /** Applies a function to all filtered element of the outer collection. */
    def foreach[U](f: A => U): Unit = {
      for (x <- self) {
        if (p(x)) f(x)
      }
    }

    /** Further refines the filter of this collection. */
    override def withFilter(q: A => Boolean): WithFilter = new WithFilter(x => p(x) && q(x))
  }

  /** Finds the first element of the $coll for which the given partial
    * function is defined, and applies the partial function to it.
    */
  def collectFirst[B](pf: PartialFunction[A, B]): Option[B] = {
    for (x <- self) {
      if (pf.isDefinedAt(x)) {
        return Some(pf(x))
      }
    }
    None
  }

  /** Builds a new collection by applying a partial function to all elements of this collection on which the function
    * is defined.
    */
  def collect[B](pf: PartialFunction[A, B]): Iterable[B] = {
    val elements = mutable.Queue.empty[B]
    for (x <- self) {
      if (pf.isDefinedAt(x)) {
        elements.append(pf(x))
      }
    }
    elements
  }
}
