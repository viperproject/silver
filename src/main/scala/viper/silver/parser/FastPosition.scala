// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver


import com.google.common.cache.{Cache, CacheBuilder}
import scala.util.parsing.input.{NoPosition, Position}

class PositionMap {
    val memo : Cache[AnyRef,AnyRef] =
    CacheBuilder.newBuilder ().weakKeys ().build ()

    def get (t : Any) : Option[Position] = {
      Option (memo.getIfPresent (t).asInstanceOf[Position])
    }

    def put (t : Any, u : Position) {
      memo.put (t.asInstanceOf[AnyRef], u.asInstanceOf[AnyRef])
    }

    def putIfNotPresent (t : Any, u : Position) {
      if (!hasBeenComputedAt (t))
        put (t, u)
    }

    def hasBeenComputedAt (t : Any) : Boolean =
      get (t) != None

    def clear(): Unit = {
      memo.invalidateAll()
    }
}


object FastPositions {

    private val MapStart = new PositionMap
    private val MapFinish = new PositionMap

    def getStart (t : Any) : Position =
      MapStart.get (t).getOrElse (NoPosition)

    def getFinish (t : Any) : Position =
      MapFinish.get (t).getOrElse (NoPosition)

    def setStart (t : Any, p : Position, force : Boolean = false) {
      if (force)
        MapStart.put(t, p)
      else
        MapStart.putIfNotPresent(t, p)
    }

    def setFinish (t : Any, p : Position, force : Boolean = false) {
      if (force)
        MapFinish.put(t, p)
      else
        MapFinish.putIfNotPresent(t, p)
    }

    def reset(): Unit = {
      MapStart.clear()
      MapFinish.clear()
    }
}

