// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver


import com.google.common.cache.{Cache, CacheBuilder}
import scala.util.parsing.input.Position

class PositionMap {
    val memo : Cache[AnyRef,AnyRef] =
    CacheBuilder.newBuilder ().weakKeys ().build ()

    def get (t : Any) : Option[Position] = {
      Option (memo.getIfPresent (t).asInstanceOf[Position])
    }

    def put (t : Any, u : Position): Unit = {
      memo.put (t.asInstanceOf[AnyRef], u.asInstanceOf[AnyRef])
    }

    def putIfNotPresent (t : Any, u : Position): Unit = {
      if (!hasBeenComputedAt (t))
        put (t, u)
    }

    def hasBeenComputedAt (t : Any) : Boolean =
      get (t) != None

    def clear(): Unit = {
      memo.invalidateAll()
    }
}