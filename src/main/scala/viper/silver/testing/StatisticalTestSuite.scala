package viper.silver.testing

import java.io.File
import java.nio.file.Path

import viper.silver
import viper.silver.utility.{Paths, TimingUtils}
import viper.silver.verifier.{AbstractError, AbstractVerificationError, Failure, Success, Verifier}

import scala.collection.immutable

trait StatisticalTestSuite extends SilSuite {

  protected def warmupLocationEnvVarName: String
  protected def targetLocationEnvVarName: String

  private def warmupDirName: Option[String] = Option(System.getenv(warmupLocationEnvVarName))
  private def targetDirName: String = Option(System.getenv(targetLocationEnvVarName)).get

  protected def numOfExecutions: Int = 1

  protected def verifier: Verifier
  override def verifiers = Vector(verifier)

  override def testDirectories: Seq[String] = warmupDirName match {
    case Some(w) =>
      Vector(w, targetDirName)
    case None =>
      Vector(targetDirName)
  }

  override def getTestDirPath(testDir: String): Path = {
    require(testDir != null, "test directory does not exist")
    val targetPath: File = Paths.canonize(testDir)
    require(targetPath.isDirectory, "invalid test directory")
    targetPath.toPath
  }

  override def systemsUnderTest:Seq[silver.testing.SystemUnderTest] = Vector(testingInstance)

  protected def name: String = "Viper Statistics"

  private val testingInstance: SystemUnderTest with TimingUtils = new SystemUnderTest with TimingUtils {

    val projectInfo = new ProjectInfo(List(name))

    override def run(input: AnnotatedTestInput): Seq[AbstractOutput] = {

      val phaseNames: Seq[String] = frontend(verifier, input.files).phases.map(_.name) :+ "Overall"

      val isWarmup = warmupDirName.isDefined && Paths.isInSubDirectory(Paths.canonize(warmupDirName.get), input.file.toFile)
      val reps = if (isWarmup) 1 else numOfExecutions

      //      println(s">>> isWarmup = $isWarmup")
      //      println(s">>> reps = $reps")

      // collect data
      val data = for (iter <- 1 to reps) yield {
        val fe = frontend(verifier, input.files)

        // collect timings
        val perPhaseTimings = fe.phases.map { p =>
          time(p.action)._2
        }

        // it is sufficient to collect errors once
        val actualErrors: Seq[AbstractError] = if (iter == 1) {
          fe.result match {
            case Success => Nil
            case Failure(es) => es collect {
              case e: AbstractVerificationError =>
                e.transformedError()
              case rest: AbstractError => rest
            }
          }
        } else Seq()

        (actualErrors, perPhaseTimings)
      }

      //      println(data)

      val (verResults: immutable.Seq[Seq[AbstractError]], timeResults: immutable.Seq[Seq[Long]]) = data.unzip

      val timingsWithTotal: Vector[Seq[Long]] = timeResults.toVector.map(row => row :+ row.sum)

      val sortedTimings = timingsWithTotal.sortBy(_.last)

      //      println(s">>> sortedTimings = ${sortedTimings}")
      //      println(s">>> sortedTimings.slice(1,reps-1) = ${sortedTimings.slice(1,reps-1)}")

      val (trimmedTimings, isTrimmed) = if (reps >= 3) {
        (sortedTimings.slice(1,reps-1), true)
      } else {
        (sortedTimings, false)
      }
      val meaningfulReps = trimmedTimings.length

      require(trimmedTimings.nonEmpty)

      //      println(s"Should be sorted: $sortedTimings")

      val meanTimings: Seq[Long] = trimmedTimings.transpose.map(col => (col.sum.toFloat / col.length).toLong)
      val bestRun: Seq[Long] = trimmedTimings.head
      val medianRun: Seq[Long] = trimmedTimings(meaningfulReps / 2)
      val worstRun: Seq[Long] = trimmedTimings.last

      //      println(s">>> min = ${bestRun.map(formatTimeForTable)}")
      //      println(s">>> max = ${worstRun.map(formatTimeForTable)}")

      if (isWarmup) {
        info(s"[JVM warmup] Time required: ${printableTimings(meanTimings, phaseNames)}.")

      } else if (meaningfulReps == 1) {
        info(s"[Benchmark] Time required: ${printableTimings(meanTimings, phaseNames)}.")

      } else {
        if (isTrimmed) {
          info(s"[Benchmark] Trimmed ${sortedTimings.length - trimmedTimings.length} marginal runs.")
        }

        val n = "%2d".format(meaningfulReps)
        info(s"[Benchmark] Mean / $n runs: ${printableTimings(meanTimings, phaseNames)}.")
        info(s"[Benchmark] Best run:       ${printableTimings(bestRun, phaseNames)}.")
        info(s"[Benchmark] Median run:     ${printableTimings(medianRun, phaseNames)}.")
        info(s"[Benchmark] Worst run:      ${printableTimings(worstRun, phaseNames)}.")
      }

      verResults.flatten.map(SilOutput)
    }

    private def printableTimings(timings: Seq[Long], phaseNames: Seq[String]): String =
      timings.map(formatTimeForTable).zip(phaseNames).map(tup => tup._1 + " (" + tup._2 + ")").mkString(", ")
  }
}

