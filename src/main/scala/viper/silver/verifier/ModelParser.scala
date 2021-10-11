package viper.silver.verifier

import java.util.regex.{Matcher, Pattern}
import scala.collection.mutable
import fastparse._
import viper.silver.parser.FastParser.whitespace

object ModelParser {
  def identifier[B: P]: P[Unit] = P(CharIn("0-9", "A-Z", "a-z", "[]\"'#++--*/:=!$_@<>.%~") ~~ CharIn("0-9", "A-Z", "a-z", "[]\"'#++--*/:=!$_@<>.%~").repX)

  def idnuse[B: P]: P[String] = P(identifier).!.filter(a => a != "else" && a != "let" && a != "->")

  def numeral[B: P]: P[Unit] = P(CharIn("0-9") ~~ CharIn("0-9").repX)

  def modelEntry[B: P]: P[(String, ModelEntry)] = P(idnuse ~ "->" ~ definition)

  def definition[B: P]: P[ModelEntry] = P(mapping | value)

  def mapping[B: P]: P[MapEntry] = P("{" ~/ mappingContent ~ "}")

  def mappingContent[B: P]: P[MapEntry] = P(options | default)

  def options[B: P]: P[MapEntry] = P(option.rep ~ "else" ~ "->" ~ value).map {
    case (options, default) => MapEntry(options.toMap, default)
  }

  def option[B: P]: P[(Seq[ValueEntry], ValueEntry)] = P(value.rep(1) ~ "->" ~/ value)

  def default[B: P]: P[MapEntry] = P(value)
    .map { default => MapEntry(Map.empty, default).resolveFunctionDefinition }

  def value[B: P]: P[ValueEntry] = P(let | constant | application)

  def let[B: P]: P[ValueEntry] = {
    def substitute(entry: ValueEntry, binding: (String, ValueEntry)): ValueEntry =
      entry match {
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

  def binding[B: P]: P[(String, ValueEntry)] = P("(" ~ idnuse ~ value ~ ")")

  def constant[B: P]: P[ConstantEntry] = P(idnuse).map(ConstantEntry.apply)

  def application[B: P]: P[ApplicationEntry] = P("(" ~ idnuse ~ value.rep ~ ")")
    .map { case (name, arguments) => ApplicationEntry(name, arguments) }

  def model[B: P]: P[Model] = P(Start ~ modelEntry.rep ~ End)
    .map { entries =>
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
