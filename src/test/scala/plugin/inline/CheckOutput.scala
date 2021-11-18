package plugin.inline{
  import org.scalatest.FunSuite

  class CheckOutput extends FunSuite with InlineTestFixture {
    test("CheckOutput") {
      val fileName = "aatree"

      val res = parse_inline(fileName)
      println(res)
    }
  }
}