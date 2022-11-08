package viper.silver.verifier

import fastparse._
object ModelParser {
  def modelEntry[_: P]: P[(String, ModelEntry)] = {
    implicit val ws = viper.silver.parser.FastParserCompanion.whitespaceWithoutNewlineOrComments
    P(idnuse ~ "->" ~ definition.?).map {
      case (i, Some(e)) => (i, e)
      case (i, None) => (i, UnspecifiedEntry)
    }
  }

  import viper.silver.parser.FastParserCompanion.whitespace

  // note that the dash/minus character '-' needs to be escaped by double backslashes such that it is not interpreted as a range
  def identifier[_: P]: P[Unit] = P(CharIn("0-9", "A-Z", "a-z", "[]\"'#+\\-*/:=!$_@<>.%~").repX(1))

  def idnuse[_: P]: P[String] = P(identifier).!.filter(a => a != "else" && a != "let" && a != "->")

  def numeral[_: P]: P[Unit] = P(CharIn("0-9").repX(1))

  def definition[_: P]: P[ModelEntry] = P(mapping | value)

  def mapping[_: P]: P[MapEntry] = P("{" ~/ mappingContent ~ "}")

  def mappingContent[_: P]: P[MapEntry] = P(options | default)

  // options consists of at least one option. If there are no options but only a single default value, the `default`
  // parser in `mappingContent` handles this case.
  def options[_: P]: P[MapEntry] = P(option.rep(1) ~ ("else" ~ "->" ~ value).?).map {
    case (options, default) => MapEntry(options.toMap, default.getOrElse(UnspecifiedEntry))
  }

  def option[_: P]: P[(Seq[ValueEntry], ValueEntry)] = P(value.rep(1) ~ "->" ~ value)

  // depending on Z3 options, we seem to get an "else ->" before the default value
  // or not, so we match both.
  def default[_: P]: P[MapEntry] = P(("else" ~ "->").? ~ value)
    .map { default => MapEntry(Map.empty, default).resolveFunctionDefinition }

  def value[_: P]: P[ValueEntry] = P(unspecified | let | constant | application)

  def let[_: P]: P[ValueEntry] = {
    def substitute(entry: ValueEntry, binding: (String, ValueEntry)): ValueEntry =
      entry match {
        case UnspecifiedEntry =>
          UnspecifiedEntry
        case ConstantEntry(value) =>
          binding match {
            case (`value`, replacement) => replacement
            case _ => entry
          }
        case ApplicationEntry(name, arguments) =>
          val substituted = arguments.map { argument => substitute(argument, binding) }
          ApplicationEntry(name, substituted)
      }

    P("(let" ~ "(" ~ binding.rep(1) ~ ")" ~ value ~ ")")
      .map { case (bindings, body) =>
        bindings.foldLeft(body) {
          case (current, binding) => substitute(current, binding)
        }
      }
  }

  def binding[_: P]: P[(String, ValueEntry)] = P("(" ~ idnuse ~ value ~ ")")

  def unspecified[_: P]: P[ValueEntry] = P("(#unspecified)").map(_ => UnspecifiedEntry)

  def constant[_: P]: P[ConstantEntry] = P(idnuse).map(ConstantEntry)

  def application[_: P]: P[ApplicationEntry] = P("(" ~ idnuse ~ value.rep ~ ")")
    .map { case (name, arguments) => ApplicationEntry(name, arguments) }

  def model[_: P]: P[Model] = P(Start ~ modelEntry.rep ~ End)
    .map { entries2Model }

  def entries2Model(entries: Seq[(String, ModelEntry)]): Model = {
    val empty = Map.empty[String, ModelEntry]
    val result = entries.foldLeft(empty) {
      case (current, (key, entry: MapEntry)) =>
        current.get(key) match {
          case Some(existing: MapEntry) =>
            val combined = MapEntry(existing.options ++ entry.options, existing.default)
            current.updated(key, combined)
          case _ => current.updated(key, entry)
        }
      case (current, (key, entry)) => current.updated(key, entry)
    }
    Model(result)
  }
}
