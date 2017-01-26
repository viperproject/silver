package viper.silver.ast.utility

/**
  * Created by simonfri on 20.12.2016.
  *
  * Trait Rewritable provides an interface that specifies which methods are required for the rewriter to work with.
  * For classes that implement product (especially case classes) everything is already implemented here and one only has to extend this base class
  */
trait Rewritable[A <: Rewritable[A]] {

  /**
    * Method that accesses all children of a node. Will be either a node or a traversable of a node
    * @return
    */
  def getChildren: Seq[Any] = {
    this match {
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
  }

  def getFlatChildren: Seq[Rewritable[A]] = {
    val children: Seq[Seq[Rewritable[A]]] = this match {
      case p: Product =>
        ((0 until p.productArity) map { x: Int => p.productElement(x) }) collect {
          case s: Seq[Rewritable[A]] => s.asInstanceOf[Seq[Rewritable[A]]]
          case o: Option[Rewritable[A]] => if(o.isDefined) Seq(o.get) else Seq[Rewritable[A]]()
          case i: Rewritable[A] => Seq(i)
        }
      case rest =>
        println("We do not support nodes that don't implement product")
        Seq()
    }
    children.foldLeft[Seq[Rewritable[A]]](Seq[Rewritable[A]]())(_ ++ _)
  }

  // Duplicate children. Children list must be in the same order as in getChildren
  def duplicate(children: Seq[Any]): A

}
