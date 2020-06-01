package viper.silver.verifier

import java.util.regex.{Matcher, Pattern}

import viper.silver.parser.FastParser.PWrapper

import scala.collection.mutable


object ModelParser {
  val White = PWrapper {
    import fastparse.all._

    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }

  import fastparse.noApi._

  import White._

  lazy val identifier: P[Unit] = P(CharIn('0' to '9', 'A' to 'Z', 'a' to 'z', "+-*/:=!$_@<>.%~") ~~ CharIn('0' to '9', 'A' to 'Z', 'a' to 'z', "+-*/:=!$_@<>.%~").repX)

  lazy val idnuse: P[String] = P(identifier).!.filter(a => a != "else" && a != "let" && a != "->")

  lazy val numeral = P(CharIn('0' to '9') ~~ CharIn('0' to '9').repX)

  lazy val modelEntry : P[(String, ModelEntry)] = P(idnuse ~ "->" ~ definition)

  lazy val definition: P[ModelEntry] = P(mapping | valueAsSingle)

  lazy val mapping: P[MapEntry] = P("{" ~/ mappingContent ~"}")

  lazy val mappingContent = P(options | valueAsElse)

  lazy val options: P[MapEntry] = P(option.rep(min=1) ~ "else" ~ "->" ~ value).map{
    case (options, els) => MapEntry(options.toMap, els)
  }

  lazy val option = P(value.rep(min=1) ~ "->" ~/ value)

  lazy val value: P[String] = P(idnuse | let | application)

  lazy val valueAsSingle : P[SingleEntry] = P(value).map(SingleEntry)

  lazy val valueAsElse : P[MapEntry] = P(value).map{
    case v => {
      boolFuncDef.parse(v) match {
        case Parsed.Success(e, _) => e
        case _ => MapEntry(Map(), v)
      }
    }
  }

  lazy val let : P[String] = P("(let" ~ "(" ~ vardef.rep(min=1) ~ ")" ~ value ~ ")").map{
    case (defs, body) =>
      defs.foldLeft(body)((currentBody, definition) => currentBody.replaceAll(Pattern.quote(definition._1), Matcher.quoteReplacement(definition._2)))
  }

  lazy val vardef : P[(String, String)] = P("(" ~ idnuse ~ value ~")")

  lazy val application: P[String] = P("(" ~ value.rep(min=1) ~")").!

  lazy val partsOfApplication: P[Seq[String]] = P("(" ~ value.rep(min=1) ~")")

  lazy val model : P[Model] = P(Start ~ modelEntry.rep ~ End).map(entries => {
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

  lazy val boolFuncDef: P[MapEntry] = P(Start ~ alternatives ~ End).map{
    case options => MapEntry(options.map(lhs => lhs -> "true").toMap, "false")
  }

  lazy val alternatives: P[Seq[Seq[String]]] = P(singleAlternative | multipleAlternatives)

  lazy val multipleAlternatives = P("(or" ~ boolOption.rep(min=1) ~")")

  lazy val singleAlternative: P[Seq[Seq[String]]] = P(boolOption).map(Seq(_))

  lazy val boolOption: P[Seq[String]] = P("(and"~ equality.rep(min=1) ~")")

  lazy val equality: P[String] = P("(=" ~ "(:var" ~ numeral ~")" ~ idnuse  ~ ")")

  def getApplication(s: String) = {
    partsOfApplication.parse(s) match {
      case Parsed.Success(parts, _) => parts
      case _ => sys.error("This case should be impossible")
    }
  }

}
