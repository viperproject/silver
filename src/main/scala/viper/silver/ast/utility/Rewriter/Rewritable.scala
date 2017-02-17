package viper.silver.ast.utility.Rewriter

/**
  * Trait Rewritable provides an interface that specifies which methods are required for the rewriter to work with.
  * For classes that implement product (especially case classes) everything is already implemented here and one only has to extend this base class
  */
trait Rewritable {

  /**
    * Method that accesses all children of a node. If a child is a collection of AST nodes we only allow Seq or Option as collections.
    * @return Sequence of children
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

  /**
    * Duplicate children. Children list must be in the same order as in getChildren
    * @param children New children for this node
    * @return Duplicated node
    */
  def duplicate(children: Seq[Any]): Any

}
