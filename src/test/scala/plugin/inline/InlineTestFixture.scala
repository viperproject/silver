import TestHelpers.MockSilFrontend
package plugin.inline {
  import org.scalatest.matchers.should.Matchers.fail
  import viper.silver.ast._
  import viper.silver.plugin.standard.inline.InlinePredicatePlugin

  import java.nio.file.Paths

  trait InlineTestFixture {

    def programCopy(
                     domains: Seq[Domain] = Seq(),
                     fields: Seq[Field] = Seq(),
                     functions: Seq[Function] = Seq(),
                     predicates: Seq[Predicate] = Seq(),
                     methods: Seq[Method] = Seq(),
                     extensions: Seq[ExtensionMember] = Seq()
                   ): Program =
      Program.apply(
        domains, fields, functions, predicates, methods, extensions
      )()

    def parse(fileName: String): Program = {
      val frontend = new MockSilFrontend
      val fileRes = getClass.getResource(s"$fileName.vpr")
      assert(fileRes != null, s"File $fileName not found")
      val file = Paths.get(fileRes.toURI)
      frontend.translate(file) match {
        case (Some(p), _) => p
        case (None, errors) => fail("Problem with program: " + errors)
      }
    }

    def parse_inline(fileName: String): Program = {
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
      inliner.beforeVerify(src)
    }
  }
}
