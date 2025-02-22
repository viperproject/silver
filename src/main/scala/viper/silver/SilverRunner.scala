package viper.silver


import scala.collection.immutable.ArraySeq
import viper.silver.frontend.DefaultStates 
import viper.silver.frontend.ViperAstProvider
import viper.silver.logger.SilentLogger
import viper.silver.reporter.NoopReporter


object SilverRunner extends SilverRunnerInstance {
  def main(args: Array[String]): Unit = {
    runMain(args)
  }
}

class SilverRunnerInstance extends ViperAstProvider(NoopReporter, SilentLogger().get) {
  def runMain(args: Array[String]): Unit = {
    var exitCode = 1 /* Only 0 indicates no error */

    execute(ArraySeq.unsafeWrapArray(args))
    
    if (state >= DefaultStates.Translation) {
      exitCode = 0
    }
    sys.exit(exitCode)
  }
}