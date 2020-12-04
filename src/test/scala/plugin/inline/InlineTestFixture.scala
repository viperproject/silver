package plugin.inline

import viper.silver.ast._

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
}
