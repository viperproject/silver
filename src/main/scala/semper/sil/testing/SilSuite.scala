package semper.sil.testing

import java.io.File
import semper.sil.verifier.{VerificationError, Success, Verifier}
import semper.source.Translator
import org.scalatest._
import java.nio.file.Path
import io.Source
import semper.sil.ast.source.RealSourceLocation

/** A test suite for verification toolchains that use SIL as the intermediate language.
  *
  * @author Stefan Heule
  */
abstract class SilSuite extends FunSuite with TestAnnotationParser {

  /** The directories (relative to `baseDirectory` where tests can be found. */
  def testDirectories: Seq[String]

  /** The base directory for tests. */
  def baseDirectory: Path

  /** The translator to be used. */
  def translator(verifier: Verifier, input: String): Translator

  /** The list of verifiers to be used. */
  def verifiers: Seq[Verifier]

  /** The config map passed to ScalaTest. */
  protected var configMap: Map[String, Any] = _

  private var _testsRegistered = false

  /** Registers a tests that runs the translator for all given verifiers. */
  def registerSilTest(file: File, prefix: String) {
    require(file != null)
    require(verifiers != null)

    val input = Source.fromFile(file).mkString
    val testName = prefix + file.getName
    val testAnnotations = parseAnnotations(input)
    var testErrors: List[String] = Nil

    // ignore test if necessary
    if (testAnnotations.isFileIgnored) {
      ignore(testName) {}
      return
    }

    // error for parse failures of test annotations
    if (testAnnotations.hasErrors) {
      testErrors ::= "Encountered the following errors while parsing the test-annotations (these annotations will be ignored):\n" + testAnnotations.errors.map("  " + _.errorMessage).mkString("\n")
    }

    // one test per verifier
    for (verifier <- verifiers) {
      test(testName + " [" + verifier.name + "]") {
        val t = translator(verifier, input)
        val (_, tParse) = time {
          t.parse
        }
        val (_, tTypeCheck) = time {
          t.typecheck
        }
        val (_, tTranslate) = time {
          t.translate
        }
        val (result, tVerification) = time {
          t.verify
        }
        assert(result != null)

        // postprocessing of errors: match up expected errors with actual errors and report inconsistencies
        var expectedButMissingErrors: List[ExpectedError] = Nil
        var unexpectedButMissingErrors: List[UnexpectedError] = Nil
        var missingButPresentErrors: List[MissingError] = Nil
        var additionalErrors: List[VerificationError] = Nil
        result match {
          case Success =>
            // no actual errors, thus there should not be any expected ones
            testAnnotations.annotations foreach {
              case e: ExpectedError => expectedButMissingErrors ::= e
              case u: UnexpectedError => unexpectedButMissingErrors ::= u
              case m: MissingError => // it is known that this one is missing
            }
          case semper.sil.verifier.Error(actualErrors) => {
            var expectedErrors = testAnnotations.errorAnnotations
            val findError: VerificationError => Option[ErrorAnnotation] = (actual: VerificationError) => {
              if (!actual.sourceLocation.isInstanceOf[RealSourceLocation]) None
              else expectedErrors.filter({
                case ErrorAnnotation(id, lineNr) => actual.fullId == id && actual.sourceLocation.asInstanceOf[RealSourceLocation].line == lineNr
              }) match {
                case x :: _ => {
                  // remove the error from the list of expected errors (i.e. only match once)
                  expectedErrors = expectedErrors.filter(y => !y.eq(x))
                  Some(x)
                }
                case Nil => None
              }
            }

            // go through all actual errors and try to match them up with the expected ones
            actualErrors foreach (a => findError(a) match {
              case Some(m@MissingError(_, _, _, _, _)) =>
                missingButPresentErrors ::= m
              case Some(_) => // expected this error
              case None =>
                additionalErrors ::= a
            })

            // process remaining errors that have not been matched
            expectedErrors.foreach({
              case e: ExpectedError => expectedButMissingErrors ::= e
              case u: UnexpectedError => unexpectedButMissingErrors ::= u
              case m: MissingError => // it is known that this one is missing
            })
          }
        }

        if (!additionalErrors.isEmpty) {
          testErrors ::= "The following errors occured during verification, but should not have according to the test annotations:\n" +
            additionalErrors.reverse.map("  " + _.toString).mkString("\n")
        }

        if (!expectedButMissingErrors.isEmpty) {
          testErrors ::= "The following errors were expected according to the test annotations, but did not occur during verification:\n" +
            expectedButMissingErrors.reverse.map("  " + _.toString).mkString("\n")
        }

        if (!unexpectedButMissingErrors.isEmpty) {
          testErrors ::= "The following errors were specified to occur erroreanously (UnexpectedError) according to the test annotations, but did not occur during verification (this might be cause by invalid test anntoations):\n" +
            unexpectedButMissingErrors.reverse.map("  " + _.toString).mkString("\n")
        }

        if (!missingButPresentErrors.isEmpty) {
          testErrors ::= "The following errors were specified to be missing erroreanously (MissingError) according to the test annotations, but did occur during verification (this might be cause by invalid test anntoations):\n" +
            missingButPresentErrors.reverse.map("  " + _.toString).mkString("\n")
        }

        // report some other useful information
        info("Verifier used: %s v%s.".format(verifier.name, verifier.version))
        info("Time required: %s (parsing), %s (typechecking), %s (translation), %s (verification).".format(tParse, tTypeCheck, tTranslate, tVerification))

        // if there were any errors that could not be matched up (or other problems), make the test fail
        if (!testErrors.isEmpty) {
          fail(testErrors.mkString("\n\n") + "\n\n")
        }
      }
    }
  }

  /** Formats a time in milliseconds. */
  def formatTime(millis: Long): String = {
    if (millis > 1000) "%.2f sec".format(millis * 1.0 / 1000)
    else "%s msec".format(millis.toString)
  }

  /** Measures the time it takes to execute `f` and returns the result of `f` as well as the required time. */
  def time[T](f: () => T): (T, String) = {
    val start = System.currentTimeMillis()
    val r = f.apply()

    (r, formatTime(System.currentTimeMillis() - start))
  }

  /** Registers all the files in a given directory as a test. */
  def registerTestDirectory(dir: File, prefix: String = "") {
    require(dir != null)

    if (dir.listFiles == null) return

    val newPrefix = prefix + dir.getName + "/"
    val namePattern = configMap.getOrElse("include", ".*").toString

    for (f: File <- dir.listFiles.filter(x => x != null && x.isDirectory)) {
      registerTestDirectory(f, newPrefix)
    }

    for (f: File <- dir.listFiles
                       .filterNot(_.isDirectory)
                       .filter(_.getCanonicalPath().matches(namePattern))) {

      registerSilTest(f, newPrefix)
    }
  }

  /** Register all the tests. */
  def registerTests() {
    if (_testsRegistered) return

    for (testDir <- testDirectories) {
      registerTestDirectory(baseDirectory.resolve(testDir).toFile)
    }

    _testsRegistered = true
  }

  override def testNames = {
    registerTests()
    super.testNames
  }

  protected override def runTest(testName: String, reporter: Reporter, stopper: Stopper, configMap: Map[String, Any], tracker: Tracker) {
    this.configMap = configMap
    registerTests()
    super.runTest(testName, reporter, stopper, configMap, tracker)
  }

  protected override def runTests(testName: Option[String], reporter: Reporter, stopper: Stopper, filter: Filter, configMap: Map[String, Any], distributor: Option[Distributor], tracker: Tracker) {
    this.configMap = configMap
    registerTests()
    super.runTests(testName, reporter, stopper, filter, configMap, distributor, tracker)
  }

  override def run(testName: Option[String], reporter: Reporter, stopper: Stopper, filter: Filter, configMap: Map[String, Any], distributor: Option[Distributor], tracker: Tracker) {
    this.configMap = configMap
    registerTests()
    super.run(testName, reporter, stopper, filter, configMap, distributor, tracker)
  }
}
