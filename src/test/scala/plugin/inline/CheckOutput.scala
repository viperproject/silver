package plugin.inline{
  import org.scalatest.funsuite.AnyFunSuite

  class CheckOutput extends AnyFunSuite with InlineTestFixture {
    test("CheckOutput") {
      val fileName = "aatree"

      val res = parse_inline(fileName)
      println(res)
    }
  }
}