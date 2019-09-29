// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.testing

import org.scalatest._
import java.nio.file.{Path, Files}
import scala.collection.JavaConverters._

/** A test suite for end-to-end toolchain testing that operates on source files
  * in resource directories.
  *
  * This abstract class is agnostic w.r.t. to the kind of testing performed
  * on the test input. It just locates the test files and builds the test input.
  * Subclasses need to implement the actual testing logic in `registerTest`.
  *
  */
abstract class ResourceBasedTestSuite extends FunSuite {
  // Subclasses can extend the test input with further information
  // such as annotations
  type InputType <: TestInput

  /**
   * The test directories where tests can be found.
   *
   * Unless your test suite overrides [[getTestDirPath]],
   * each of the directories in [[testDirectories]] must be relative
   * because they are resolved via [[java.lang.ClassLoader]] in the
   * default implementation.
   * @see http://stackoverflow.com/a/7098501/491216.
   *
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

  val defaultTestPattern: String = ".*(\\.sil|\\.vpr)"

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

    val directoryStream = Files.newDirectoryStream(dir).asScala
    val dirContent = directoryStream.toList
    val includeFilesPattern = configMap.getOrElse("includeFiles", defaultTestPattern).toString

    for (f: Path <- dirContent.sorted
         if Files.isDirectory(f)) {

      val newPrefix = prefix + "/" + f.getName(f.getNameCount - 1)
      registerTestDirectory(f, newPrefix)
    }

    for (f: Path <- dirContent.sorted
        // If a file is renamed while Sbt runs, AccessDeniedExceptions
        // might be thrown. Apparently, because the old file still exists in
        // target/.../test-classes, but it is somehow locked. Weird stuff.
        // Once the SBT REPL is closed, the "ghost" file disappears.
        if Files.isReadable(f)
        if !Files.isDirectory(f)
        if f.toString.matches(includeFilesPattern)) {

      val testInput = buildTestInput(f, prefix)

      if (   testInput.files.head == f /* Only register multi file tests once, not for every contained file */
          && isTestToBeIncluded(testInput)) /* Include tests based on arguments passed to test runner */ {

        registerTest(testInput)
      }
    }
  }

  /** Decides if a test input is to be included based on (command-line) arguments
    * passed to the test runner. That is, tests can be explicitly included by
    * passing `-n SomeTag`, respectively, excluded by passing `-l SomeTag` when
    * invoking the test runner. See ScalaTest's user guide for more information.
    *
    * Note that tests marked to be ignored are considered to be included. The
    * reason for this is that they will be ignored (i.e., not executed) by
    * ScalaTest later on anyway, in which case a corresponding message will be
    * logged that might be of interest to the user.
    *
    * @param testInput A test input
    * @return True iff the test is to be included
    */
  protected def isTestToBeIncluded(testInput: InputType): Boolean = {
    this.optFilter match {
      case None => true

      case Some(filter) =>
        val tags = Map(testInput.name -> testInput.tags.map(_.name).toSet)
        val (filterTest, _ /*ignoreTest*/) = filter(testInput.name, tags, "ResourceBasedTestSuite")
        !filterTest /*&& !ignoreTest*/
    }
  }

  private var _testsRegistered = false

  protected def getTestDirPath(testDir: String): Path = {
    val resource = classLoader.getResource(testDir)
    assert(resource != null, s"Test directory $testDir couldn't be found")
    viper.silver.utility.Paths.pathFromResource(classLoader.getResource(testDir))
  }

  private def registerTests() {
    if (_testsRegistered) return

    // Here, the order of elements in testDirectories is defined
    //  by the test suite implementation and we need not sort it.
    for (testDir <- testDirectories) {
      val path = getTestDirPath(testDir)
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

  override def testNames = {
    registerTests()
    super.testNames
  }

  /** The config map passed to ScalaTest. */
  protected var configMap: Map[String, Any] = Map[String, Any]()

  /** The filter passed to one of the `run`-methods. */
  protected var optFilter: Option[Filter] = None

  protected override def runTest (
      testName: String,
      args : Args) : Status =
    {

    this.configMap = args.configMap

    registerTests()

    super.runTest(testName, args)
  }

  protected override def runTests(
      testName: Option[String],
      args: Args) : Status = {

    this.configMap = args.configMap
    this.optFilter = Some(args.filter)

    registerTests()

    super.runTests(testName, args)
  }

  override def run(
      testName: Option[String],
      args : Args) : Status  = {

    this.configMap = args.configMap
    this.optFilter = Some(args.filter)

    registerTests()

    super.run(testName, args)
  }
}
