package viper.silver.ast.utility

/**
  * Created by simonfri on 20.12.2016.
  *
  * Trait Rewritable provides an interface that specifies which methods are required for the rewriter to work with.
  * For classes that implement product (especially case classes) everything is already implemented here and one only has to extend this base class
  */
trait Rewritable {

  /**
    * Method that accesses all children of a node. Will be either a node or a traversable of a node
    * @return
    */
  def getChildren: Seq[Any] = {
    this match {
      case p: Product =>
        ((0 until p.productArity) map { x: Int => p.productElement(x) }) collect {
          case s: Seq[Rewritable] => s
          case o: Option[Rewritable] => o
          case i: Rewritable => i
        }
      case rest =>
        println("We do not support nodes that don't implement product")
        Seq()
    }
  }

  def getFlatChildren: Seq[Rewritable] = {
    val children: Seq[Seq[Rewritable]] = this match {
      case p: Product =>
        ((0 until p.productArity) map { x: Int => p.productElement(x) }) collect {
          case s: Seq[Rewritable] => s.asInstanceOf[Seq[Rewritable]]
          case o: Option[Rewritable] => if(o.isDefined) Seq(o.get) else Seq[Rewritable]()
          case i: Rewritable => Seq(i)
        }
      case rest =>
        println("We do not support nodes that don't implement product")
        Seq()
    }
    children.foldLeft[Seq[Rewritable]](Seq[Rewritable]())(_ ++ _)
  }

  // Duplicate children. Children list must be in the same order as in getChildren
  def duplicate(children: Seq[Any]): Any

}

trait RewritableCompanion {
  def isMyType(a: Any): Boolean
}
