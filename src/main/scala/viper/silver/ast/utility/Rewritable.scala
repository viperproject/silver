package viper.silver.ast.utility

/**
  * Created by simonfri on 20.12.2016.
  *
  * Trait Rewritable provides an interface that specifies which methods are required for the rewriter to work with.
  * For classes that implement product (especially case classes) everything is already implemented here and one only has to extend this base class
  */
trait Rewritable[A <: Rewritable[A]] {

  private var transformed = false

  def wasTransformed = transformed
  def setTransformed(b: Boolean) = transformed = b

  /**
    * Method that accesses all children of a node. Will be either a node or a traversable of a node
    * @return
    */
  def getChildren: Seq[Any] = {
    val thisNode = this
    val childs: Seq[Any] = thisNode match {
      case p: Product =>
        ((0 until p.productArity) map { x: Int => p.productElement(x) }) collect {
          case s: Seq[Rewritable[A]] => s
          case o: Option[Rewritable[A]] => o
          case i: Rewritable[A] => i
        }
      case rest =>
        println("We do not support nodes that don't implement product")
        Seq()
    }

    childs
  }

  // Duplicate children. Children list must be in the same order as in getChildren
  def duplicate(children: Seq[Any]): A = ???

  def duplicateNode(children:Seq[Any]): A = {
    val a = duplicate(children)
    a.setTransformed(true)
    a
  }

}
