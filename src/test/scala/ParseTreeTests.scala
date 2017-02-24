
import java.nio.file.{Path, Paths}

import org.scalatest.{FunSuite, Matchers}
import viper.silver._
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter._
import viper.silver.ast.utility._
import viper.silver.frontend.{SilFrontend, TranslatorState}
import viper.silver.verifier.AbstractError

import scala.collection.mutable
import scala.language.implicitConversions


class ParseTreeTests extends FunSuite {
  test("CyclicMacroDetection") {
    val filePrefix = "parsertests\\cyclicMacros\\"
    val files = Seq("simple", "complex", "complexExp")

    val frontend = new DummyFrontend

    files foreach { fileName => {
      val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
      assert(fileRes != null, s"File $filePrefix$fileName not found")
      val file = Paths.get(fileRes.toURI)
      var targetNode: Node = null

      frontend.translate(file) match {
        case (Some(p), _) => println("Everything ok, but we expected cyclic error!"); assert(false)
        case (None, errors) => errors.foreach( e => { println("Error: " + e); assert(e.readableMessage.contains("Recursive macro declaration found")) })
      }
    }
    }
  }

  test("MacroExpansion") {
    val filePrefix = "parsertests\\macroExpansion\\"
    //val files = Seq("simple", "simple2", "simpleExp", "simpleArgs", "simpleArgs2", "simpleArgsExp", "simpleMethod", "simpleMethodExp")
    val files = Seq("simpleMethodExp")

    val frontend = new DummyFrontend

    files foreach { fileName => {
      val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
      assert(fileRes != null, s"File $filePrefix$fileName" + ".sil not found")
      val file = Paths.get(fileRes.toURI)

      val fileRef = getClass.getResource(filePrefix + fileName + "Ref" + ".sil")
      assert(fileRef != null, s"File $filePrefix$fileName"+ "Ref.sil not found")
      val fileR = Paths.get(fileRef.toURI)

      var targetNode: Node = null
      var targetRef: Node = null

      frontend.translate(file) match {
        case (Some(p), _) => targetNode = p
        case (None, errors) => println("error occured during translating: " + errors)
      }

      frontend.translate(fileR) match {
        case (Some(p), _) => targetRef = p
        case (None, errors) => println("error occured during translating: " + errors)
      }

      println("New: " + targetNode.toString())
      println("Reference: " + targetRef.toString())
      assert(targetNode.toString() == targetRef.toString(), "Files are not equal")
    }
    }

  }

}