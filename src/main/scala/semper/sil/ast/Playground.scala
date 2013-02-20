package semper.sil.ast

import pretty.PrettyPrinter
import semper.sil.parser.{Resolver, Translator, Parser}
import org.kiama.util.Messaging.{messagecount, sortedmessages}
import utility.Statements

// --- Playground

object Main {
  def main(args: Array[String]) {
    println("\n\n")
    //meth
    //tp
    //println(PrettyPrinter.pretty(program))
    //exp
    //parse("1+(2*(1-3))+4")
    //println(program)
    cfg
    /*parse(
      """
        |  method foo(a: Int, b: Bool)
        |    requires true
        |    ensures false
        |  {
        |    var x: Int := 1 + a
        |    var y: Int := 2 + x
        |    if (true) {
        |       y := -30;
        |    } else {
        |       x := x*x
        |    }
        |  }
      """.stripMargin
    )
    if (args.size > 0) {
      parse(args(0))
    }*/
  }

  def parse(s: String) = {
    val p = Parser.parse(s)
    p match {
      case Parser.Success(e, _) =>
        Resolver.check(e)
        if (messagecount == 0) {
          val n = Translator.translate(e)
          println(PrettyPrinter.pretty(n))
        } else {
          for (m <- sortedmessages)
            println(m)
        }
      case f => println(f)
    }
  }

  import language.implicitConversions
  implicit def lift(s: String): Info = SimpleInfo(List(s))

  lazy val n = NoPosition
  lazy val T = TypeVar("T")
  lazy val S = TypeVar("S")
  lazy val tru = TrueLit()()
  lazy val fals = FalseLit()()
  lazy val self = ThisLit()()
  lazy val domain = Domain("Map", Nil, Nil, List(T, S))()
  lazy val domainType = DomainType(domain, Map())
  lazy val domainType2 = DomainType(domain, Map(T -> Int, S -> Bool))
  def vari(s: String, t: Type) = LocalVar(s)(t)
  lazy val one = IntLit(1)()
  lazy val two = IntLit(2)()
  lazy val hundred = IntLit(100)()
  lazy val c1 = LeCmp(l4, two)()

  lazy val l1 = LocalVar("a")(Int)
  lazy val l2 = LocalVar("b")(Int)
  lazy val l3 = LocalVar("c")(domainType2)
  lazy val l4 = LocalVar("d")(Int)
  lazy val l5 = LocalVar("e")(domainType2)

  lazy val f1 = Field("val")(Int, n, "Some field description")
  lazy val f2 = Field("test")(domainType2, n, "Another comment")

  lazy val emptyStmt = Statements.EmptyStmt

  lazy val method = Method("foo", List(l1, l2), List(l3, l4), Nil, Nil, Vector(l5), emptyStmt)()

  lazy val program = Program("ListReverse", Nil, List(f1, f2), Nil, Nil, List(method))()

  lazy val if1 = If(c1,
    LocalVarAssign(l1, one)(),
    LocalVarAssign(l2, two)()
  )()

  lazy val if2 = If(c1,
    if1,
    LocalVarAssign(l2, two)()
  )()

  lazy val lbl1 = Label("lbl1")()
  lazy val lbl2 = Label("lbl2")()

  lazy val goto1 = Goto("lbl1")()
  lazy val goto2 = Goto("lbl2")()

  lazy val block1 = Seqn(Seq(
    If(c1,
      if1,
      goto1
    )(),
    Seqn(Seq(
      LocalVarAssign(l4, two)(),
      lbl1,
      LocalVarAssign(l2, two)(),
      LocalVarAssign(l2, hundred)()
    ))()
  ))()

  lazy val block2 = Seqn(Seq(
    LocalVarAssign(l4, two)(),
    loop1,
    LocalVarAssign(l1, hundred)()
  ))()

  lazy val loop1 = While(tru, Nil, Nil, block1)()

  lazy val block1b = Seqn(Seq(
    If(c1,
      if1,
      goto2
    )(),
    Seqn(Seq(
      LocalVarAssign(l4, two)(),
      lbl1,
      LocalVarAssign(l2, two)(),
      LocalVarAssign(l2, hundred)()
    ))()
  ))()

  lazy val block2b = Seqn(Seq(
    LocalVarAssign(l4, two)(),
    loop1b,
    Seqn(Seq(
      lbl2,
      LocalVarAssign(l1, hundred)()
    ))()
  ))()

  lazy val loop1b = While(tru, Nil, Nil, block1b)()

  def cfg {
    val s = block1

    printCfg(s)
  }

  def meth = {
    val m = MethodCall(method, self, List(l1, l1), List(l3, l4))()
    println(PrettyPrinter.pretty(m))
  }

  def tp = {
    println(PrettyPrinter.pretty(domainType))
    println(PrettyPrinter.pretty(domainType2))
  }

  def exp = {
    val i1 = Mul(IntLit(1)(), Add(LocalVar("a")(Int), IntLit(3)())())()
    val i2 = IntLit(0)()
    val b1 = LeCmp(i1, i2)()
    val b2 = fals
    val b3 = tru
    val r = Not(And(b1, Or(b2, b3)())())()
    println(PrettyPrinter.pretty(r))
  }

  def printCfg(b: Stmt) {
    println(b)
    printCfg(b.toCfg)
  }
  def printCfg(b: Block) {
    val file = "C:\\tmp\\sil\\cfg.dot"
    val dot = b.toDot
    val pw = new java.io.PrintWriter(new java.io.File(file))
    pw.write(dot)
    pw.close()
    println(dot)
    import scala.sys.process._
    Seq("dot", "-Tpdf", file, "-o", "C:\\tmp\\sil\\cfg.pdf").!
  }
}
