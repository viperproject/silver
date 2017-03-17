package viper.silver


import com.google.common.cache.{Cache, CacheBuilder}
import scala.util.parsing.input.{NoPosition, Position}

/**
  * Created by Sahil on 22.06.16.
  */

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

}

