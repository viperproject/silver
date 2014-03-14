package semper.sil.testing

import org.scalatest._
import java.net.{URI, URL}
import java.nio.file._
import scala.collection.JavaConversions._

/**
 * A test suite for end-to-end toolchain testing that operates on source files
 * in resource directories.
 *
 * This abstract class is agnostic w.r.t. to the kind of testing performed
 * on the test input. It just locates the test files and builds the test input.
 * Subclasses need to implement the actual testing logic in `registerTest`.
 *
 * @author Stefan Heule
 */
abstract class ResourceBasedTestSuite extends FunSuite {
  // Subclasses can extend the test input with further information
  // such as annotations
  type InputType <: TestInput

  /**
   * The test directories where tests can be found.
   * The directories must be relative because they are resolved via
   * [[java.lang.ClassLoader]].
   * @see http://stackoverflow.com/a/7098501/491216.
   * @return A sequence of test directories.
   */
  def testDirectories: Seq[String]

  /**
   * Registers a test based on the test input.
   * To be implemented by subclasses.
   * @param input the test input as built in `buildTestInput`
   */
  def registerTest(input: InputType)

  /**
   * Builds the test input from the given source file.
   *
   * @param file the canonical test source file. The test input implementation
   *             will decide what other files are part of the same test, if any
   * @param prefix part of the test file path. Together with the test file name
   *               it should uniquely identify the test
   * @return the test input
   */
  def buildTestInput(file: Path, prefix: String): InputType

  /**
   * Recursively registers all files found in the given directory as a test.
   *
   * The prefix is used for naming and tagging the ScalaTest test case that is eventually
   * generated for each test file found. Subdirectories of `dir` will be appended to the
   * initial prefix.
   *
   * It is thus reasonable to make the initial prefix the (relative) root test directory.
   * For example, given the following directories and files
   *   .../issues/test1.scala
   *              test2.scala
   *   .../all/basic/test1.scala
   *                 test2.scala
   *                 test3.scala
   * it would be reasonable to make the calls
   *   registerTestDirectory(path_of(".../issues"), "issues")
   *   registerTestDirectory(path_of(".../all/basic"), "all/basic")
   * or
   *   registerTestDirectory(path_of(".../issues"), "issues")
   *   registerTestDirectory(path_of(".../all"), "all")
   * to - in both cases - get ScalaTest test cases that can be identified by
   *   issues/test1.scala
   *   issues/test2.scala
   *   all/basic/test1.scala
   *   all/basic/test2.scala
   *   all/basic/test3.scala
   *
   * @param dir The directory to recursively search for files. Every file in the directory is
   *            assumed to be a test file.
   * @param prefix The initial prefix used for naming and tagging the resulting ScalaTest tests.
   */
  private def registerTestDirectory(dir: Path, prefix: String) {
    assert(dir != null, "Directory must not be null")
    assert(Files.isDirectory(dir), "Path must represent a directory")

    val directoryStream = Files.newDirectoryStream(dir)
    val dirContent = directoryStream.toList
    val namePattern = configMap.getOrElse("includeTests", ".*\\.sil").toString

    for (f: Path <- dirContent
         if Files.isDirectory(f)) {

      val newPrefix = prefix + "/" + f.getName(f.getNameCount - 1)
      registerTestDirectory(f, newPrefix)
    }

    for (f: Path <- dirContent
        // If a file is renamed while Sbt runs, AccessDeniedExceptions
        // might be thrown. Apparently, because the old file still exists in
        // target/.../test-classes, but it is somehow locked. Weird stuff.
        // Once the SBT REPL is closed, the "ghost" file disappears.
        if Files.isReadable(f)
        if !Files.isDirectory(f)
        if f.toString.matches(namePattern)) {

      val testInput = buildTestInput(f, prefix)

      // The files that belong to the same test.
      if (testInput.files.head == f) {
        // Only register the multi file test once, not for every file it contains.
        registerTest(testInput)
      }
    }
  }

  private var _testsRegistered = false

  private def registerTests() {
    if (_testsRegistered) return

    for (testDir <- testDirectories) {
      val resource = classLoader.getResource(testDir)
      assert(resource != null, s"Test directory $testDir couldn't be found")

      val path = pathFromResource(classLoader.getResource(testDir))
      registerTestDirectory(path, testDir)
    }

    _testsRegistered = true
  }

  /**
   * Returns a class loader that can be used to access resources
   * such as test files via [[java.lang.ClassLoader]].
   *
   * @return A class loader for accessing resources.
   */
  private def classLoader: ClassLoader = getClass.getClassLoader

  private var openFileSystems: Seq[FileSystem] = Seq()
  addShutdownHookForOpenFileSystems()

  /**
   * Creates a path from the given URL, which, for example, could have been
   * obtained by calling [[java.lang.ClassLoader]]. The current implementation
   * can handle URLs that point into the normal file system (file:...) or
   * into a jar file (jar:...).
   *
   * Based on code taken from http://stackoverflow.com/a/15718001/491216.
   *
   * @param resource The URL to turn into a path.
   * @return The path obtained from the URL.
   */
  private def pathFromResource(resource: URL): Path = {
    assert(resource != null, "Resource URL must not be null")

    val uri = resource.toURI

    uri.getScheme match {
      case "file" => Paths.get(uri)

      case "jar" =>
        val uriStr = uri.toString
        val separator = uriStr.indexOf("!/")
        val entryName = uriStr.substring(separator + 2)
        val fileURI = URI.create(uriStr.substring(0, separator))

        // 2013-05-03 Malte:
        // The following bit of code is quite nasty, but I wasn't able to get anything less
        // nasty to work reliably. There are two main problems:
        //
        // 1. It is not obvious when to close the file system, because several components of
        //    our tool chain keep references to path objects that in turn have references
        //    to their underlying file system. If these path objects are used (not all usages
        //    seem dangerous, though) after the underlying file system has been closed, an
        //    exception is thrown.
        //
        // 2. If the test suite is executed from an Sbt prompt then the shutdown hook of
        //    the runtime environment doesn't seem to fire and the file systems don't seem
        //    to be closed. Thus, if the tests are executed again without existing the
        //    Sbt prompt, FileSystemAlreadyExistsExceptions can be thrown because some
        //    file systems are still open.
        //
        // The list of open file systems (openFileSystems) unfortunately doesn't seem to
        // survive, otherwise it might have been possible to maintain a map from file URI
        // to file system and only create a new file system if there is no map entry for
        // the given file URI yet.
        //
        // I also tried to use a finalizer method instead of the shutdown hook, but the
        // finalizer also doesn't seem to be called if the Sbt prompt is not existed.

        var fs: FileSystem = null

        try {
          fs = FileSystems.newFileSystem(fileURI, Map[String, Object]())
          openFileSystems = fs +: openFileSystems
        } catch {
          case e: java.nio.file.FileSystemAlreadyExistsException =>
            fs = FileSystems.getFileSystem(fileURI)
            assert(fs.isOpen, "The reused file system is expected to still be open")
        } finally {
          assert(fs != null, s"Could not get hold of a file system for $fileURI (from $uriStr)")
        }

        fs.getPath(entryName)

      case other => sys.error(s"Resource $uri of scheme $other is not supported.")
    }
  }

  /** Closes all open file systems stored in `openFileSystems`. */
  private def addShutdownHookForOpenFileSystems() {
    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run() {
        if (openFileSystems != null) {
          openFileSystems foreach (fs => if (fs.isOpen) {fs.close()})
        }
      }
    })
  }

  override def testNames = {
    registerTests()
    super.testNames
  }

  /** The config map passed to ScalaTest. */
  protected var configMap: Map[String, Any] = Map[String, Any]()

  protected override def runTest(
      testName: String,
      reporter: Reporter,
      stopper: Stopper,
      configMap: Map[String, Any],
      tracker: Tracker) {
    this.configMap = configMap
    registerTests()
    super.runTest(testName, reporter, stopper, configMap, tracker)
  }

  protected override def runTests(
      testName: Option[String],
      reporter: Reporter,
      stopper: Stopper,
      filter: Filter,
      configMap: Map[String, Any],
      distributor: Option[Distributor],
      tracker: Tracker) {
    this.configMap = configMap
    registerTests()

    super.runTests(testName, reporter, stopper, filter, configMap, distributor, tracker)
  }

  override def run(
      testName: Option[String],
      reporter: Reporter,
      stopper: Stopper,
      filter: Filter,
      configMap: Map[String, Any],
      distributor: Option[Distributor],
      tracker: Tracker) {
    this.configMap = configMap
    registerTests()
    super.run(testName, reporter, stopper, filter, configMap, distributor, tracker)
  }
}
