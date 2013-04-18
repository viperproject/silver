package semper.sil.testing

import java.io.File
import semper.sil.verifier._
import java.nio.file.Path
import io.Source
import semper.sil.ast.{Position, TranslatedPosition, SourcePosition}
import org.scalatest._
import semper.sil.frontend.Frontend
import java.util.regex.Pattern

/** A test suite for verification toolchains that use SIL as the intermediate language.
  *
  * Note that tests are named by the first file for a given test, e.g. `basic/functions.sil`.
  * The tests are also tagged by their name and by the file name (with and without extension);
  * in the example the tags would be `basic/functions.sil`, `functions.sil` and `functions`.
  * These tags can be used to execute just a single test:
  * `test-only * -- -n functions`
  *
  * @author Stefan Heule
  */
abstract class SilSuite extends FunSuite with TestAnnotationParser {

  /** The directories (relative to `baseDirectory` where tests can be found. */
  def testDirectories: Seq[String]

  /** The base directory for tests. */
  def baseDirectory: Path

  /** The frontend to be used. */
  def frontend(verifier: Verifier, files: Seq[File]): Frontend

  /** The list of verifiers to be used. */
  def verifiers: Seq[Verifier]

  /** The config map passed to ScalaTest. */
  protected var configMap: Map[String, Any] = _

  private var _testsRegistered = false

  def testName(prefix: String, files: Seq[File]) = files match {
    case f :: Nil => prefix + f.getName
    case f :: _ => prefix + fileListName(f)
    case _ => prefix
  }

  val fileListRegex = """(.*)_file\d*.*""".r

  def fileListName(f: File) = f.getName match {
    case fileListRegex(name) => name
    case name => name
  }

  def fileList(file: File): Seq[File] = file.getName match {
    case fileListRegex(name) => {
      val regex = (Pattern.quote(name) + """_file(\d*).*""").r
      var files = List[(File, Int)]()
      file.getParentFile.listFiles.foreach(f => f.getName match {
        case regex(index) => files = (f, index.toInt) :: files
        case _ => ()
      })
      files.sortBy(_._2).map(_._1)
    }
    case _ => Seq(file)
  }

  /** Registers a tests that runs the translator for all given verifiers. */
  def registerSilTest(file: File, prefix: String) {
    require(file != null)
    require(verifiers != null)

    val rawFiles = fileList(file)
    if (rawFiles.head != file) {
      // Only register the file list once, not for every file it contains.
      return
    }
    val name = testName(prefix, rawFiles)
    val testAnnotations = parseAnnotations(rawFiles)
    val files = rawFiles filter { f => !testAnnotations.isFileIgnored(f) }
    val fileName = file.getName
    val fileNameWithoutExt = fileName.substring(0, fileName.lastIndexOf("."))

    // ignore test if necessary
    if (files.isEmpty) {
      ignore(name, Tag(name), Tag(fileName), Tag(fileNameWithoutExt)) {}
      return
    }

    var testErrors: List[String] = Nil

    // error for parse failures of test annotations
    if (testAnnotations.hasErrors) {
      testErrors ::= "Encountered the following errors while parsing the test-annotations (these annotations will be ignored):\n" + testAnnotations.errors.map("  " + _.errorMessage).mkString("\n")
    }

    // one test per verifier
    for (verifier <- verifiers) {
      test(name + " [" + verifier.name + "]", Tag(name), Tag(fileName), Tag(fileNameWithoutExt)) {
        val fe = frontend(verifier, List(file))
        val tPhases = fe.phases.map { p =>
          time(p.action)._2 + " (" + p.name + ")"
        }.mkString(", ")
        val result = fe.result
        assert(result != null)

        // postprocessing of errors: match up expected errors with actual errors and report inconsistencies
        var expectedButMissingErrors: List[ExpectedError] = Nil
        var unexpectedButMissingErrors: List[UnexpectedError] = Nil
        var missingButPresentErrors: List[MissingError] = Nil
        var additionalErrors: List[AbstractError] = Nil
        result match {
          case Success =>
            // no actual errors, thus there should not be any expected ones
            testAnnotations.annotations foreach {
              case e: ExpectedError => expectedButMissingErrors ::= e
              case u: UnexpectedError => unexpectedButMissingErrors ::= u
              case m: MissingError => // it is known that this one is missing
              case _: IgnoreOthers =>
              case _: IgnoreFileList =>
                sys.error("the test should not have run in the first place")
              case _: IgnoreFile => () // Could be that some files of this test, but not all of them are ignored.
            }
          case Failure(actualErrors) => {
            var expectedErrors = testAnnotations.errorAnnotations
            def sameLine(file: File, lineNr: Int, pos: Position) = pos match {
              case p: SourcePosition => lineNr == p.line
              case p: TranslatedPosition => file == p.file && lineNr == p.line
              case _ => sys.error("Position is neither a source position nor a translated position even though we checked this before.")
            }
            val findError: AbstractError => Option[TestAnnotation] = (actual: AbstractError) => {
              if (!actual.pos.isInstanceOf[SourcePosition] && !actual.pos.isInstanceOf[TranslatedPosition]) None
              else expectedErrors.filter({
                case ErrorAnnotation(id, file, lineNr) => id.matches(actual.fullId) && sameLine(file, lineNr, actual.pos)
                case IgnoreOthers(file, lineNr, _) => sameLine(file, lineNr, actual.pos)
              }) match {
                case Nil => None
                case l => l.find(_.isInstanceOf[ErrorAnnotation]) match {
                  case Some(x) => {
                    // remove the error from the list of expected errors (i.e. only match once)
                    expectedErrors = expectedErrors.filter(y => !y.eq(x))
                    Some(x)
                  }
                  case None => Some(l.head) // IgnoreOthers should not be removed
                }
              }
            }

            // go through all actual errors and try to match them up with the expected ones
            actualErrors foreach (a => findError(a) match {
              case Some(m: MissingError) =>
                missingButPresentErrors ::= m
              case Some(_) => // expected this error
              case None =>
                additionalErrors ::= a
            })

            // process remaining errors that have not been matched
            expectedErrors.foreach {
              case e: ExpectedError => expectedButMissingErrors ::= e
              case u: UnexpectedError =>
                if (u.project.toLowerCase == verifier.name.toLowerCase) unexpectedButMissingErrors ::= u
              case _: MissingError => // Expected to be missing
              case _: IgnoreOthers =>
            }
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
        info(s"Verifier used: ${verifier.name} ${verifier.version}.")
        verifier.dependencies foreach {
          dep =>
            info(s"  using ${dep.name} ${dep.version} located at ${dep.location}")
        }
        info(s"Time required: $tPhases.")

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
      .filter(_.getCanonicalPath.matches(namePattern))) {

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
