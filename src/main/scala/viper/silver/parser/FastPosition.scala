package viper.silver


import com.google.common.cache.{Cache, CacheBuilder}


/**
  * Created by sahil on 22.06.16.
  */

trait Memoiser {




  private var memoVersion = 0

  def resetMemo () {
    memoVersion += 1
  }


  trait MemoisedBase[T,U] {


    def memo : Cache[AnyRef,AnyRef]


    private var thisMemoVersion = 0


    def dup (t1 : T, t2 : T, u : U) {
      resetIfRequested ()
      put (t2, getWithDefault (t1, u))
    }


    def get (t : T) : Option[U] = {
      resetIfRequested ()
      Option (memo.getIfPresent (t).asInstanceOf[U])
    }


    def getWithDefault (t : T, u : U) : U =
      get (t).getOrElse (u)

    def put (t : T, u : U) {
      resetIfRequested ()
      memo.put (t.asInstanceOf[AnyRef], u.asInstanceOf[AnyRef])
    }


    def putIfNotPresent (t : T, u : U) {
      resetIfRequested ()
      if (!hasBeenComputedAt (t))
        put (t, u)
    }


    def reset () {
      memo.invalidateAll ()
    }


    def resetAt (t : T) {
      memo.invalidate (t)
    }


    def hasBeenComputedAt (t : T) : Boolean =
      get (t) != None


    def resetIfRequested () {
      if (thisMemoVersion != memoVersion) {
        thisMemoVersion = memoVersion
        reset ()
      }
    }

  }




  trait IdMemoised[T,U] extends MemoisedBase[T,U] {

    val memo : Cache[AnyRef,AnyRef] =
      CacheBuilder.newBuilder ().weakKeys ().build ()

  }

}



object FastPositions extends Memoiser {


  import scala.util.parsing.input.{NoPosition, Position}


  class FPositionMap extends IdMemoised[Any,Position]


  private val FstartMap = new FPositionMap


  private val FfinishMap = new FPositionMap


  def getStart[T] (t : T) : Position =
    FstartMap.getWithDefault (t, NoPosition)


  def getFinish[T] (t : T) : Position =
    FfinishMap.getWithDefault (t, NoPosition)


  def setStart[T] (t : T, p : Position) {
    FstartMap.putIfNotPresent (t, p)
  }


  def setFinish[T] (t : T, p : Position) {
    FfinishMap.putIfNotPresent (t, p)
  }


  /*def positionAt (l : Int, c : Int) : Position =
    new Position {
      val line = l
      val column = c
      val lineContents = ""
    }*/




}

