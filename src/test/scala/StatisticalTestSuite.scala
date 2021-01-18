package viper.silver.testing

import java.io.{BufferedWriter, File, FileWriter}
import java.nio.file.{Path, Paths => JPaths}
import scala.collection.immutable
import org.scalatest.ConfigMap
import viper.silver
import viper.silver.utility.{Paths, TimingUtils}
import viper.silver.verifier.{AbstractError, AbstractVerificationError, Failure, Success, Verifier}

trait StatisticalTestSuite extends SilSuite {
  protected def repetitionsPropertyName: String = "STATS_REPETITIONS"
  protected def warmupLocationPropertyName: String = "STATS_WARMUP"
  protected def targetLocationPropertyName: String = "STATS_TARGET"
  protected def csvFilePropertyName: String = "STATS_CSV"
  protected def inclusionFilePropertyName: String = "STATS_INCL_FILE"

  protected def repetitions: Int =
    Option(System.getProperty(repetitionsPropertyName)) match {
      case Some(reps) =>
        val intReps = reps.toInt

        failIf(
          s"Repetitions must be >= 1, but got $reps",
          intReps < 1)

        intReps
      case None =>
        val default = 1
        info(s"[StatisticalTestSuite] Repetitions defaults to $default")

        default
    }

  protected def warmupDirName: Option[String] = {
    val dir = System.getProperty(warmupLocationPropertyName, "").trim

    if (dir.isEmpty) None
    else Option(dir)
  }

  protected def targetDirName: String =
    Option(System.getProperty(targetLocationPropertyName)) match {
      case Some(name) => name
      case None => fail(s"Property '$targetLocationPropertyName' not set")
    }

  protected def csvFileName: Option[String] = getNonEmptyOptionalSystemProperty(csvFilePropertyName)
  protected def inclusionFileName: Option[String] = getNonEmptyOptionalSystemProperty(inclusionFilePropertyName)

  protected def verifier: Verifier
  override def verifiers = Vector(verifier)

  private var csvFile: BufferedWriter = _

  private var testsToInclude: Option[Set[String]] = None

  override def testDirectories: Seq[String] = warmupDirName match {
    case Some(w) =>
      Vector(w, targetDirName)
    case None =>
      Vector(targetDirName)
  }

  override def getTestDirPath(testDir: String): Path = {
    failIf(s"Test directory '$testDir' does not exist", testDir == null)

    val targetPath: File = Paths.canonize(testDir)
    failIf(s"Invalid test directory '$testDir'", !targetPath.isDirectory)

    targetPath.toPath
  }

  override def beforeAll(configMap: ConfigMap): Unit = {
    super.beforeAll(configMap)

    csvFileName foreach (filename => {
      csvFile = new BufferedWriter(new FileWriter(filename))

      csvFile.write("File,Outputs,Mean [ms],StdDev [ms],RelStdDev [%],Best [ms],Median [ms],Worst [ms]")
      csvFile.newLine()
      csvFile.flush()
    })

    inclusionFileName foreach (filename => {
      // TODO: Replace try-catch with scala.util.Using once Viper switched to Scala 2.13

      val source = scala.io.Source.fromFile(filename)

      try {
        testsToInclude = Some(source.getLines().toSet)
      } finally {
        source.close()
      }
    })
  }

  override def afterAll(configMap: ConfigMap): Unit = {
    super.afterAll(configMap)

    if (csvFileName.isDefined) csvFile.close()
  }

  override def systemsUnderTest:Seq[silver.testing.SystemUnderTest] = Vector(testingInstance)

  protected def name: String

  private val testingInstance: SystemUnderTest with TimingUtils = new SystemUnderTest with TimingUtils {

    /** In order to support hierarchical test annotations (an UnexpectedError could be attributed to a verifier, e.g.
      * Silicon, or generally to Silver), it is important to extend (update) the project info field, not to overwrite
      * it. See also [[SilSuite.projectInfo]].
      */
    lazy val projectInfo: ProjectInfo = StatisticalTestSuite.this.projectInfo.update(name)

    override def run(input: AnnotatedTestInput): Seq[AbstractOutput] = {
      testsToInclude foreach (tests => {
        if (!tests.contains(input.name)) {
          alert(s"Skipping ${input.name} (not included)")

          return Seq.empty // Don't execute the current test
        }
      })

      val phaseNames: Seq[String] = frontend(verifier, input.files).phases.map(_.name) :+ "Overall"

      val isWarmup = warmupDirName.isDefined && Paths.isInSubDirectory(Paths.canonize(warmupDirName.get), input.file.toFile)
      val reps = if (isWarmup) 1 else repetitions

      //      println(s">>> isWarmup = $isWarmup")
      //      println(s">>> reps = $reps")

      // collect data
      val data = for (_ <- 1 to reps) yield {
        val fe = frontend(verifier, input.files)

        // collect timings
        val perPhaseTimings = fe.phases.map { p =>
          time(p.f)._2
        }

        val actualErrors: Seq[AbstractError] =
          fe.result match {
            case Success => Nil
            case Failure(es) => es collect {
              case e: AbstractVerificationError =>
                e.transformedError()
              case rest: AbstractError => rest
            }
          }

        (actualErrors, perPhaseTimings)
      }

      //      println(data)

      val (verResults: immutable.Seq[Seq[AbstractError]], timeResults: immutable.Seq[Seq[Long]]) = data.unzip

      if (1 < verResults.length) {
        Predef.assert(
          verResults.tail.forall(_ == verResults.head),
          s"Did not get the same errors for all repetitions: $verResults")
      }

      val timingsWithTotal: Vector[Seq[Long]] = timeResults.toVector.map(row => row :+ row.sum)

      val sortedTimings = timingsWithTotal.sortBy(_.last)

      //      println(s">>> sortedTimings = ${sortedTimings}")
      //      println(s">>> sortedTimings.slice(1,reps-1) = ${sortedTimings.slice(1,reps-1)}")

      val (trimmedTimings, isTrimmed) = if (reps >= 4) {
        (sortedTimings.slice(1,reps-1), true)
      } else {
        (sortedTimings, false)
      }
      val meaningfulReps = trimmedTimings.length

      Predef.assert(trimmedTimings.nonEmpty)

      //      println(s"Should be sorted: $sortedTimings")

      val meanTimings: Seq[Long] = trimmedTimings.transpose.map(col => (col.sum.toFloat / col.length).toLong)
      val bestRun: Seq[Long] = trimmedTimings.head
      val medianRun: Seq[Long] = trimmedTimings(meaningfulReps / 2)
      val worstRun: Seq[Long] = trimmedTimings.last

      val stddevTimings = trimmedTimings.transpose.zip(meanTimings).map { case (col, mean) =>
        math.sqrt(col.map(v => math.pow((v - mean).toDouble, 2)).sum / col.length).toLong
      }

      val relStddevTimings = stddevTimings.zip(meanTimings).map { case (stddev, mean) =>
        (100.0 * stddev / math.abs(mean)).toLong
      }

      //      println(s">>> min = ${bestRun.map(formatTimeForTable)}")
      //      println(s">>> max = ${worstRun.map(formatTimeForTable)}")

      if (isWarmup) {
        info(s"[JVM warmup] Time required: ${printableTimings(meanTimings, phaseNames)}.")
      } else if (meaningfulReps == 1) {
        info(s"[Benchmark] Time required: ${printableTimings(meanTimings, phaseNames)}.")

        if (csvFileName.isDefined) {
          val csvRowData = Seq(
            JPaths.get(targetDirName).toAbsolutePath.relativize(input.file.toAbsolutePath),
            verResults.head.length,
            meanTimings.last, stddevTimings.last, relStddevTimings.last,
            bestRun.last, medianRun.last, worstRun.last)

          csvFile.write(csvRowData.mkString(","))
          csvFile.newLine()
          csvFile.flush()
        }
      } else {
        if (isTrimmed) {
          info(s"[Benchmark] Trimmed ${sortedTimings.length - trimmedTimings.length} marginal runs.")
        }

        val n = "%2d".format(meaningfulReps)
        info(s"[Benchmark] Mean / $n runs: ${printableTimings(meanTimings, phaseNames)}.")
        info(s"[Benchmark] Stddevs:        ${printableTimings(stddevTimings, phaseNames)}.")
        info(s"[Benchmark] Rel. stddev:    ${printablePercentage(relStddevTimings, phaseNames)}.")
        info(s"[Benchmark] Best run:       ${printableTimings(bestRun, phaseNames)}.")
        info(s"[Benchmark] Median run:     ${printableTimings(medianRun, phaseNames)}.")
        info(s"[Benchmark] Worst run:      ${printableTimings(worstRun, phaseNames)}.")

        if (csvFileName.isDefined) {
          val csvRowData = Seq(
            JPaths.get(targetDirName).toAbsolutePath.relativize(input.file.toAbsolutePath),
            verResults.head.length,
            meanTimings.last, stddevTimings.last, relStddevTimings.last,
            bestRun.last, medianRun.last, worstRun.last)

          csvFile.write(csvRowData.mkString(","))
          csvFile.newLine()
          csvFile.flush()
        }
      }

      verResults.flatten.map(SilOutput)
    }

    private def printableTimings(timings: Seq[Long], phaseNames: Seq[String]): String =
      timings.map(formatTimeForTable).zip(phaseNames).map(tup => tup._1 + " (" + tup._2 + ")").mkString(", ")

    private def printablePercentage(percentage: Seq[Long], phaseNames: Seq[String]): String = {
      percentage
        .map(p => "%6s %%   ".format(p)) /*** Format in sync with [[formatTimeForTable()]] */
        .zip(phaseNames)
        .map(tup => tup._1 + " (" + tup._2 + ")")
        .mkString(", ")
    }
  }

  private def failIf(message: => String, condition: Boolean): Unit =
    if (condition) fail(message)

  private def getNonEmptyOptionalSystemProperty(key: String): Option[String] = {
    val value = System.getProperty(key, "").trim

    if (value.isEmpty) None
    else Some(value)
  }
}

