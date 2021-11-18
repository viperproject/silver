


import TestHelpers.{FileComparisonHelper, MockSilFrontend}

package plugin.inline{
  import org.scalatest.FunSuite
  import viper.silver.ast.Program
  import viper.silver.plugin.standard.inline.InlinePredicatePlugin

  import java.nio.file.Paths

  class CheckOutput extends FunSuite with FileComparisonHelper {
    test("CheckOutput") {
      val fileName = "recursive"

      val frontend = new MockSilFrontend
      val fileRes = getClass.getResource(s"$fileName.vpr")
      assert(fileRes != null, s"File $fileName not found")
      val file = Paths.get(fileRes.toURI)
      val src: Program = frontend.translate(file) match {
        case (Some(p), _) => p
        case (None, errors) => fail("Problem with program: " + errors)
      }
      val inliner = frontend.plugins.plugins.collectFirst({
        case p: InlinePredicatePlugin => p;
      }).get
      println(src)
      val res = inliner.beforeVerify(src)
      println(res)
    }
  }
}