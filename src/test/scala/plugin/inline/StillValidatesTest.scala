import TestHelpers.MockSilFrontend
package plugin.inline {
  import org.scalatest.funsuite.AnyFunSuite
  import viper.silver.plugin.standard.inline.InlineErrorChecker

  import java.nio.file.Files

  class StillValidatesTest extends AnyFunSuite with InlineErrorChecker with InlineTestFixture {
    def testProgram(fileName: String): Unit = {
      val inlined = parse_inline(fileName).toString()
      val file = Files.createTempFile("prefix", "suffix")
      Files.writeString(file, inlined)
      try {
        (new MockSilFrontend).translate(file)
      } catch {
        case e: Throwable =>
          fail(inlined)
      }
    }

    test("aatree") { testProgram("aatree")}
    test("assert-invariant") { testProgram("assert-invariant")}
    test("chonker") { testProgram("chonker")}
    test("different-field-types") { testProgram("different-field-types")}
    test("empty") { testProgram("empty")}
    test("function") { testProgram("function")}
    test("impure-branch") { testProgram("impure-branch")}
    test("inline") { testProgram("inline")}
    test("max-array-standard") { testProgram("max-array-standard")}
    test("minimal") { testProgram("minimal")}
    test("multi-rec") { testProgram("multi-rec")}
    test("mutrec") { testProgram("mutrec")}
    test("nested") { testProgram("nested")}
    test("perm_none") { testProgram("perm_none")}
    test("permission-propagation") { testProgram("permission-propagation")}
    test("recursive") { testProgram("recursive")}
    test("sum") { testProgram("sum")}
    test("tuple") { testProgram("tuple")}
    test("unfold-arity-one") { testProgram("unfold-arity-one")}
    test("unfolding") { testProgram("unfolding")}


  }
}


