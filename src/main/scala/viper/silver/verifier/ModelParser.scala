package viper.silver.verifier

import java.util.regex.{Matcher, Pattern}
import scala.collection.mutable
import fastparse._
import viper.silver.parser.FastParser.whitespace
import viper.silver.parser.FastParser.P

object ModelParser {

  def identifier[_: P]: P[Unit] = P(CharIn("0-9", "A-Z", "a-z", "[]\"'#+-*/:=!$_@<>.%~") ~~ CharIn("0-9", "A-Z", "a-z", "[]\"'#+-*/:=!$_@<>.%~").repX)

  def idnuse[_: P]: P[String] = P(identifier).!.filter(a => a != "else" && a != "let" && a != "->")

  def numeral[_: P] = P(CharIn("0-9") ~~ CharIn("0-9").repX)

  def modelEntry[_: P] : P[(String, ModelEntry)] = P(idnuse ~ "->" ~ definition)

  def definition[_: P]: P[ModelEntry] = P(mapping | valueAsSingle)

  def mapping[_: P]: P[MapEntry] = P("{" ~/ mappingContent ~"}")

  def mappingContent[_: P] = P(options | valueAsElse)

  def options[_: P]: P[MapEntry] = P(option.rep(0) ~ "else" ~ "->" ~ value).map{
    case (options, els) => MapEntry(options.toMap, els)
  }

  def option[_: P] = P(value.rep(1) ~ "->" ~/ value)

  def value[_: P]: P[String] = P(idnuse | let | application)

  def valueAsSingle[_: P] : P[SingleEntry] = P(value).map(SingleEntry)

  def valueAsElse[_: P] : P[MapEntry] = P(value).map{
    case v => {
      parse(v, boolFuncDef(_)) match {
        case Parsed.Success(e, _) => e
        case _ => MapEntry(Map(), v)
      }
    }
  }

  def let[_: P] : P[String] = P("(let" ~ "(" ~ vardef.rep(1) ~ ")" ~ value ~ ")").map{
    case (defs, body) =>
      defs.foldLeft(body)((currentBody, definition) => currentBody.replaceAll(Pattern.quote(definition._1), Matcher.quoteReplacement(definition._2)))
  }

  def vardef[_: P] : P[(String, String)] = P("(" ~ idnuse ~ value ~")")

  def application[_: P]: P[String] = P("(" ~ value.rep(1) ~")").!

  def partsOfApplication[_: P]: P[Seq[String]] = P("(" ~ value.rep(1) ~")")

  def model[_: P] : P[Model] = P(Start ~ modelEntry.rep ~ End).map(entries => {
    val res: mutable.Map[String, ModelEntry] = mutable.Map()
    for ((name, entry) <- entries) {
      if (res.contains(name)){
        val currentEntry = res.get(name).get
        // presumably, these are both MapEntries; otherwise how can they be differentiated
        if (entry.isInstanceOf[MapEntry] && currentEntry.isInstanceOf[MapEntry]){
          val currentMap = currentEntry.asInstanceOf[MapEntry]
          val newMap = entry.asInstanceOf[MapEntry]
          res.update(name, MapEntry(currentMap.options ++ newMap.options, currentMap.els))

        }
      }else{
        res.update(name, entry)
      }
    }
    Model(res.toMap)
  })

  def boolFuncDef[_: P]: P[MapEntry] = P(Start ~ alternatives ~ End).map{
    case options => MapEntry(options.map(lhs => lhs -> "true").toMap, "false")
  }

  def alternatives[_: P]: P[Seq[Seq[String]]] = P(singleAlternative | multipleAlternatives)

  def multipleAlternatives[_: P] = P("(or" ~ boolOption.rep(1) ~")")

  def singleAlternative[_: P]: P[Seq[Seq[String]]] = P(boolOption).map(Seq(_))

  def boolOption[_: P]: P[Seq[String]] = P("(and"~ equality.rep(1) ~")")

  def equality[_: P]: P[String] = P("(=" ~ "(:var" ~ numeral ~")" ~ idnuse  ~ ")")

  def getApplication(s: String) = {
    parse(s, partsOfApplication(_)) match {
      case Parsed.Success(parts, _) => parts
      case _ => sys.error("This case should be impossible")
    }
  }

}
