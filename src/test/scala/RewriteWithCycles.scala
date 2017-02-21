import org.scalatest.{FunSuite, Matchers}
import viper.silver.ast.utility.Rewriter.{Query, Rewritable, StrategyBuilder}
import viper.silver.ast.utility.ViperStrategy

/**
  * Created by simonfri on 21.02.2017.
  */
class RewriteWithCycles extends FunSuite {


  test("SimpleCycle") {
    val a = SlimGraph[Int](1)
    val b = SlimGraph[Int](10, Seq(a))
    val c = SlimGraph[Int](100, Seq(b))
    a.addChildren(c)

    visitAll[Int](a, _ * 2)
    val res = Seq(a,b,c).foldLeft(0)(_ + _.info)

    assert(res == 222)
  }

  test("ComplexCycle") {
    val a = SlimGraph[Int](1)
    val b = SlimGraph[Int](10)
    val c = SlimGraph[Int](100)
    val d = SlimGraph[Int](1000)


    a.addChildren(b, c)
    b.addChildren(c)
    c.addChildren(a, d)
    d.addChildren(d)

    visitAll[Int](a, _ * 3)
    val res = Seq(a,b,c,d).foldLeft(0)(_ + _.info)

    // we visit c twice (intended because it is a shared node)
    assert( res == 3933)

  }



  // Visit all reachable nodes in the graph and call func on them.
  def visitAll[I](s:SlimGraph[I], func:I=>I) = {
    val strat = StrategyBuilder.AncestorStrategy[SlimGraph[I]]({
      case (sG, c) => {
        if(c.ancestorList.dropRight(1).contains(sG))
          c.noRec(sG)
        else {
          sG.info = func(sG.info)
          sG
        }
      }
    })
    strat.execute[SlimGraph[I]](s)
  }

}

// Simple graph class. Enough to demonstrate what we want
case class SlimGraph[I](var info: I, var children: Seq[SlimGraph[I]] = Seq()) extends Rewritable {
  def addChildren(ch: SlimGraph[I]*) = children ++= ch

  override def duplicate(childr: Seq[Any]): Any = {
    info = children.collect {case i:I => i }.head
    children = childr.collect {  case s:SlimGraph[I] => s }
    this
  }

  // Otherwise toString crashes from infinite recursion
  override def toString: String = info.toString

  // Work around. Infinite hash code calculation is problem!
  override def hashCode(): Int = info.hashCode()
}
