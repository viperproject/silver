package semper.sil.frontend

import semper.source.DefaultTranslator
import semper.sil.ast._
import semper.sil.parser.{PNode, Translator, Resolver, Parser}
import org.kiama.util.Messaging._
import semper.sil.verifier._

/**
 * Common functionality to implement a command-line verifier for SIL.  This trait
 * provides code to invoke the parser, parse common command-line options and print
 * error messages in a user-friendly fashion.
 *
 * Users of this trait should implement a main method that calls `SilFrontEnd.run`.
 * Furthermore, they must implement the method `verifier` that returns a verifier
 * for SIL.
 *
 * @author Stefan Heule
 */
trait SilFrontEnd extends DefaultTranslator {

  override protected type ParserResult = PNode
  override protected type TypecheckerResult = Program

  /**
   * Main method that parses command-line arguments, parses the input file and passes
   * the SIL program to the verifier.  The resulting error messages (if any) will be
   * shown in a user-friendly fashion.
   */
  def main(args: Seq[String]) {

    val start = System.currentTimeMillis()

    // initialize the translator
    init(verifier)

    // parse command line arguments

    // run the parser, typechecker, and verifier (calling verify will do all of them)
    verify()

    val timeMs = System.currentTimeMillis() - start
    val time = s"${(timeMs / 1000)} seconds"

    // print the result
    val depToString = ((dep: (String, String)) => s"${dep._1} v${dep._2}")
    val dep = (verifier.dependencyVersions map depToString).mkString(", ")
    println(s"${verifier.name} v${verifier.version} (using $dep) finished in $time.")
    result match {
      case Success =>
        println("No errors found.")
      case Failure(errors) =>
        println("The following errors were found:")
        for (e <- errors) {
          println("  " + e.readableMessage)
        }
    }
  }

  override def doParse(input: String): Result[ParserResult] = {
    val p = Parser.parse(input)
    p match {
      case Parser.Success(e, _) =>
        Succ(e)
      case Parser.Failure(msg, next) =>
        Fail(List(ParseError(s"Failure: $msg", SourcePosition(next.pos.line, next.pos.column))))
      case Parser.Error(msg, next) =>
        Fail(List(ParseError(s"Error: $msg", SourcePosition(next.pos.line, next.pos.column))))
    }
  }

  override def doTypecheck(input: ParserResult): Result[TypecheckerResult] = {
    Resolver.check(input)
    if (messagecount == 0) {
      val n = Translator.translate(input).asInstanceOf[Program]
      Succ(n)
    } else {
      val errors = for (m <- sortedmessages) yield {
        TypecheckerError(m.message, SourcePosition(m.pos.line, m.pos.column))
      }
      Fail(errors)
    }
  }

  override def doTranslate(input: TypecheckerResult): Result[Program] = {
    // no translation needed
    Succ(input)
  }

  /** The SIL verifier to be used for verification. */
  def verifier: Verifier

}
