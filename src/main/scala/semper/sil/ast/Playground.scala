package semper.sil.ast

import pretty.PrettyPrinter
import semper.sil.parser.{Resolver, Translator, Parser}
import org.kiama.util.Messaging.{message, messagecount, report,
resetmessages, sortedmessages}

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
    parse(
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
    }
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

  implicit def lift(s: String): Info = SimpleInfo(List(s))

  val n = NoPosition
  val T = TypeVar("T")
  val S = TypeVar("S")
  val tru = TrueLit()()
  val fals = FalseLit()()
  val self = ThisLit()()
  val domain = Domain("Map", Nil, Nil, List(T, S))()
  val domainType = DomainType(domain, Map())
  val domainType2 = DomainType(domain, Map(T -> Int, S -> Bool))
  def vari(s: String, t: Type) = LocalVar(s)(t)

  val l1 = LocalVar("a")(Int)
  val l2 = LocalVar("b")(Int)
  val l3 = LocalVar("c")(domainType2)
  val l4 = LocalVar("d")(Int)
  val l5 = LocalVar("e")(domainType2)

  val f1 = Field("val")(Int, n, "Some field description")
  val f2 = Field("test")(domainType2, n, "Another comment")

  val emptyStmt = Statements.EmptyStmt

  val method = Method("foo", List(l1, l2), List(l3, l4), Nil, Nil, Vector(l5), emptyStmt)()

  val program = Program("ListReverse", Nil, List(f1, f2), Nil, Nil, List(method))()

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
}
